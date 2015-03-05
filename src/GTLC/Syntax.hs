{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fwarn-incomplete-patterns #-}

module GTLC.Syntax where

import Control.Monad.Error (Error(..), ErrorT, MonadError, throwError)
import Control.Monad.Reader (ReaderT, MonadReader, asks, local)
import Control.Monad.State (StateT, liftM, liftM2)
import Test.QuickCheck (Arbitrary, Gen, arbitrary, elements)
import Data.HashMap.Lazy as H
import qualified Data.Map.Lazy as M


data Operator = Inc | Dec | ZeroQ deriving (Show,Eq,Read)

data SExp =
  -- Surface language
  N Int
  | B Bool
  | Op Operator SExp
  | If SExp SExp SExp
  | Var Name
  | App SExp SExp
  | Lam Name SExp
  | AnnLam (Name,Type) SExp
  | GRef SExp
  | GDeRef SExp
  | GAssign SExp SExp
  | Let Name SExp SExp
  deriving (Show,Eq,Read)

data IExp = 
  --Intermediate language
  IN Int
  | IB Bool
  | IOp Operator IExp
  | IIf IExp IExp IExp
  | IVar Name
  | IApp IExp IExp
  | IAnnLam (Name,Type) IExp
  | IGRef IExp
  | IGDeRef IExp
  | IGAssign IExp IExp
  | ILet Name IExp IExp
  | IC IExp Coercion
  deriving (Show,Eq)

data Value =
  VN Int
  | VB Bool
  | Closure (Name,Type) IExp EvEnv
  | VAddr Int
  deriving (Show)

data Type =
  Dyn
  | IntTy
  | BoolTy
  | Fun Type Type
  | GRefTy Type
  deriving (Show,Eq,Read)

data Coercion = 
  IdC Type
  | InjC Type -- !
  | ProjC Type -- ?
  | FunC Coercion Coercion
  | SeqC Coercion Coercion
  | FailC Type Type
  | RefC Coercion Coercion
  deriving (Show,Eq)

type Name = String


-- | Translates values to expressions.
valToSExp :: (Value,EvHeap) -> SExp
valToSExp (VN x,_) = (N x)
valToSExp (VB x,_) = (B x)
valToSExp (Closure x e envx,h) = AnnLam x $ substIExp e envx h
valToSExp (VAddr a, hp@EvHeap{evHeap=h}) = GRef $ valToSExp $ (maybe undefined id $ H.lookup a h,hp)


-- | Substitutes variables with values in the environment and translates from the intermediate language to the surface language.
substIExp :: IExp -> EvEnv -> EvHeap -> SExp
substIExp (IN n) envx _ = N n
substIExp (IB b) envx _ = B b
substIExp (IOp op e) envx h = Op op $ substIExp e envx h
substIExp (IIf e1 e2 e3) envx h = If (substIExp e1 envx h) (substIExp e2 envx h) $ substIExp e3 envx h
substIExp (IVar x) (EvEnv envx) h = maybe (Var x) (\v->valToSExp (v,h)) (M.lookup x envx)
substIExp (IApp e1 e2) envx h = App (substIExp e1 envx h) $ substIExp e2 envx h
substIExp (IAnnLam x e) envx h = AnnLam x $ substIExp e envx h
substIExp (IGRef e) envx h = GRef $ substIExp e envx h
substIExp (IGDeRef e) envx h = GDeRef $ substIExp e envx h
substIExp (IGAssign e1 e2) envx h = GAssign (substIExp e1 envx h) $ substIExp e2 envx h
substIExp (ILet v e1 e2) envx h = Let v (substIExp e1 envx h) $ substIExp e2 envx h
substIExp (IC e _) envx h = substIExp e envx h

------------------------------------------------------------------------------------

-- Type checking environment stuff

data TyGamma = TyGamma {tyCtx :: M.Map Name Type}

data TyErr =
  -- Type Errors
  PrimitiveOperator Operator Type
  | IllTypedIfExp String
  | ArgParamMismatch Type Type
  | CallNonFunction
  | UndefinedVar Name
  | BadDereference Type
  | BadAssignment Type
  | IllTypedAssignment Type Type
  -- Cast Errors
  | CastBetweenInconsistentTypes Type Type
  -- Unknown
  | UnknownTyError String
  deriving (Eq)

instance Error TyErr where
  strMsg msg = UnknownTyError msg

instance Show TyErr where
  show (PrimitiveOperator op t) = "The argument to " ++ show op ++ " has the type " ++ show t ++ " which is not consistent"
  show (IllTypedIfExp s) = s
  show (ArgParamMismatch t1 t2) = "The argument to the function has type " ++ show t2 ++ " that is not consistent with the type of the function parameter " ++ show t1
  show CallNonFunction = "The expression in the function position is not of Function type"
  show (UndefinedVar v) = "The variable " ++ show v ++ " is not bound"
  show (CastBetweenInconsistentTypes t1 t2) = "You can not cast between " ++ show t1 ++ " and " ++ show t2 ++ " because they are inconsistent"
  show (UnknownTyError s) = s
  show (BadDereference t) = "Trying to dereference an expression of type " ++ show t ++ " which is not a reference type"
  show (BadAssignment t) = "Trying to assign an expression to another of type " ++ show t ++ " which is not a reference type"
  show (IllTypedAssignment t1 t2) = "Trying to assign an expression of type "  ++ show t2 ++ " to a reference of type " ++ show t1 ++ " and they are not consistent"


type TcMonad = ReaderT TyGamma (ErrorT TyErr IO)


-- | Look for the type of a variable in the context
-- throwing an error if the name doesn't exist.
lookupTy :: (MonadReader TyGamma m, MonadError TyErr m) => Name -> m Type
lookupTy v = asks tyCtx >>= \c -> maybe (throwError $ UndefinedVar v) return (M.lookup v c)


-- | Extend the context with a new binding.
extendTyCtx :: (MonadReader TyGamma m) => (Name, Type) -> m a -> m a
extendTyCtx (x,t) = local $ \m@(TyGamma {tyCtx = cs}) -> m {tyCtx = M.insert x t cs}


------------------------------------------------------------------------------------

-- Evaluation stuff

data EvHeap = EvHeap {evHeap :: H.HashMap Int Value, evTop :: Int} deriving Show

data EvEnv = EvEnv {evEnv :: M.Map Name Value} deriving Show

type EvMonad = StateT EvHeap (ReaderT EvEnv (ErrorT EvErr IO))


data EvErr =
  EvUnknownError String
  | EvUndefinedVar Name
  | EvCallNonFunctionNonCast
  | EvBadReference
  | EvBadLocation
  | EvCoercionFailed
  deriving (Eq)


instance Error EvErr where
  strMsg msg = EvUnknownError msg


instance Show EvErr where
  show (EvUndefinedVar v) = "The variable " ++ show v ++ " is not bound"
  show (EvUnknownError s) = s
  show EvCallNonFunctionNonCast = "The expression in the function position is neither a function nor a cast of one"
  show EvBadReference = "The expression in the reference position is not a reference"
  show EvBadLocation = "Trying to access unallocated memory location"
  show EvCoercionFailed = "Trying to coerce from one type to another and they are not consistent"


-- | Extend the evaluation environment with a new binding.
extendEvEnv :: (MonadReader EvEnv m) => (Name, Value) -> EvEnv -> m a -> m a
extendEvEnv (x,v) m@(EvEnv {evEnv = en}) = local (\_ -> m { evEnv = M.insert x v en })


------------------------------------------------------------------------------------

-- Testing stuff

data TsGamma = TsGamma {tsCtx :: M.Map Name Type, tsSize :: Int}

type TsMonad = ReaderT TsGamma Gen

-- | Changes the size field of a gamma
newSize :: Int -> TsGamma -> TsGamma
newSize n g = g{tsSize = n}


-- | Changes the size field of a gamma in reader monad
updtMSize :: Int -> TsMonad SExp -> TsMonad SExp
updtMSize = local . newSize


-- | Extend the context with a new binding, enforcing shadowing.
extendTsCtx :: (MonadReader TsGamma m) => (Name, Type) -> m a -> m a
extendTsCtx (k,v) = local (\ m@(TsGamma {tsCtx = cs}) -> m { tsCtx = M.insert k v cs })


instance Arbitrary Operator where
  arbitrary = elements [Inc,Dec,ZeroQ]


instance Arbitrary Type where
  arbitrary = liftM2 Fun arbitrary arbitrary >>= \f -> liftM GRefTy arbitrary >>= \r -> elements [IntTy, BoolTy, f, r]
