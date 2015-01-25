{-# LANGUAGE NamedFieldPuns, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module GTLC where

import Control.Monad.Error
import Control.Monad.Reader
import qualified Data.Map as Map

data Operator = Inc | Dec | ZeroQ deriving (Show,Eq,Read)
data Exp =
  N Int
  | B Bool
  | Op Operator Exp BlameLabel
  | If Exp Exp Exp BlameLabel 
  | Var Name
  | App Exp Exp BlameLabel
  | Lam Name Exp
  | AnnLam (Name,Type) Exp
  | Cast Exp BlameLabel Type
    --Intermediate language
  | IOp Operator Exp
  | ICast Exp BlameLabel Type Type
  | IApp Exp Exp
  | IIf Exp Exp Exp
  deriving (Show,Eq,Read)

data Type =
  Dyn
  | IntTy
  | BoolTy
  | Fun Type Type
  deriving (Show,Eq,Read)

type BlameLabel = String
type Name = String

-- | Computes the greatest lower bound with respect to the ordering relation “less or equally dynamic”.
meet :: Type -> Type -> Maybe Type
meet t Dyn = Just t
meet Dyn t = Just t
meet IntTy t@IntTy = Just t
meet BoolTy t@BoolTy = Just t
meet (Fun t11 t12) (Fun t21 t22) = case (meet t11 t21) of
                                    Just t1 -> case (meet t12 t22) of
                                               Just t2 -> Just (Fun t1 t2)
                                               _ -> Nothing
                                    _ -> Nothing
meet _ _ = Nothing


-- | Checks if two types are consistent.
consistentQ :: Type -> Type -> Bool
consistentQ t1 t2 = maybe False (\_ -> True) (meet t1 t2)


-- | Computes the type of a constant or operator.
typeof :: Exp -> Type
typeof (N _) = IntTy
typeof (B _) = BoolTy
typeof (Op Inc _ _) = Fun IntTy IntTy
typeof (Op Dec _ _) = Fun IntTy IntTy
typeof (Op ZeroQ _ _) = Fun IntTy BoolTy
typeof _ = undefined


-- | Wraps a run-time cast around the expression if the two types are different.
mk_cast :: BlameLabel -> Exp -> Type -> Type -> Exp
mk_cast l e t1 t2 = if t1 == t2 then e else (ICast e l t1 t2)

-- | Modeling the environment and the error monads

data Gamma = Gamma { ctx :: Map.Map Name Type }

data Err =
  -- Type Errors
  PrimitiveOperator Operator Type
  | IllTypedIfExp String
  | ArgParamMismatch Type Type
  | CallNonFunction
  | UndefinedVar Name
  -- Cast Errors
  | CastBetweenInconsistentTypes Type Type
  -- Unknown
  | UnknownError String
  deriving (Eq)

instance Error Err where
  strMsg msg = UnknownError msg

instance Show Err where
  show (PrimitiveOperator op t) = "The argument to " ++ show op ++ " has the type " ++ show t ++ " which is not consistent"
  show (IllTypedIfExp s) = s
  show (ArgParamMismatch t1 t2) = "The argument to the function has type " ++ show t2 ++ " that is not consistent with the type of the function parameter " ++ show t1
  show CallNonFunction = "The expression in the function position is not of Function type"
  show (UndefinedVar v) = "The variable " ++ show v ++ " is not bounded"
  show (CastBetweenInconsistentTypes t1 t2) = "You can not cast between " ++ show t1 ++ " and " ++ show t2 ++ " because they are inconsistent"
  show (UnknownError s) = s

type TcMonad = ErrorT Err (Reader Gamma)

-- | Look for the type of a variable in the context
-- throwing an error if the name doesn't exist.
lookupTy :: (MonadReader Gamma m, MonadError Err m) => Name -> m Type
lookupTy v = asks ctx >>= \ctx -> maybe (throwError (UndefinedVar v)) return (Map.lookup v ctx)

-- | Extend the context with a new binding.
extendCtx :: (MonadReader Gamma m) => (Name, Type) -> m a -> m a
extendCtx (x,t) = local (\ m@(Gamma {ctx = cs}) -> m { ctx = Map.insert x t cs })

-- | Type-check expression of the GTLC, converting it to one in intermediate language with explicit casts.
typecheck :: Exp -> TcMonad (Exp,Type)
typecheck e@(N _) = return (e, (typeof e))
typecheck e@(B _) = return (e, (typeof e))
typecheck e@(Op op e1 l) = typecheck e1 >>= \ (e2, t) -> let (Fun t1 t2) = typeof e in if (consistentQ t t1) then return ((IOp op (mk_cast l e2 t t1)), t2) else throwError (PrimitiveOperator op t)
typecheck (If e e1 e2 l) = typecheck e >>= \ (te, t1) -> typecheck e1 >>= \ (te1, t2) -> typecheck e2 >>= \ (te2, t3) -> if (consistentQ t1 BoolTy) && (consistentQ t2 t3) then
    case (meet t2 t3) of
     Just if_T -> return ((IIf (mk_cast l te t1 BoolTy) (mk_cast l te1 t2 if_T) (mk_cast l te2 t3 if_T)), if_T)
     Nothing -> throwError (IllTypedIfExp "The two arms of the If expression do not have consistent types")
    else
    throwError (IllTypedIfExp "The condition of the If expression is not consistent with the boolean type")
typecheck e@(Var x) = lookupTy x >>= \t -> return (e,t)
typecheck (Lam x e) = typecheck (AnnLam (x,Dyn) e)
typecheck (AnnLam v@(x,t) e) = extendCtx v (typecheck e) >>= \ (e1,t1) -> return ((AnnLam (x,t) e1),(Fun t t1))
typecheck (Cast e l t) = (typecheck e) >>= \ (e2,t2) -> if (consistentQ t2 t) then return ((mk_cast l e2 t2 t),t) else throwError (CastBetweenInconsistentTypes t2 t)
typecheck (App e1 e2 l) = typecheck e2 >>= \ (e4,t) -> (typecheck e1) >>= \ g -> case g of
                                                                                  (e3, Dyn) -> return ((IApp (mk_cast l e3 Dyn (Fun t Dyn)) e4),Dyn)
                                                                                  (e3, (Fun t21 t22)) -> if (consistentQ t t21) then return ((IApp e3 (mk_cast l e4 t (Fun t t21))), t22) else throwError (ArgParamMismatch t21 t)
                                                                                  _ -> throwError CallNonFunction
typecheck _ = undefined
