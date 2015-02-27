{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fwarn-incomplete-patterns #-}

module GTLC.Syntax where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.HashMap.Lazy as H
import qualified Data.Map as M


data Heap = Heap {heap :: H.HashMap Int Value, top :: Int} deriving Show

data Env = Env { env :: M.Map Name Value} deriving Show

type EvMonad = StateT Heap (ReaderT Env (ErrorT EvErr IO))


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
  | IC IExp Coercion
  deriving (Show,Eq)

data Value =
  VN Int
  | VB Bool
  | Closure (Name,Type) IExp Env
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
valToSExp :: Value -> SExp
valToSExp (VN x) = (N x)
valToSExp (VB x) = (B x)
valToSExp (Closure p@(x,t) e envx) = AnnLam p $ substIExp e envx


-- | Substitutes variables with values in the environment and translates from the intermediate language to the surface language.
substIExp :: IExp -> Env -> SExp
substIExp (IN n) envx = N n
substIExp (IB b) envx = B b
substIExp (IOp op e) envx = Op op $ substIExp e envx
substIExp (IIf e1 e2 e3) envx = If (substIExp e1 envx) (substIExp e2 envx) $ substIExp e3 envx
substIExp (IVar x) (Env envx) = maybe (Var x) valToSExp (M.lookup x envx)
substIExp (IApp e1 e2) envx = App (substIExp e1 envx) $ substIExp e2 envx
substIExp (IAnnLam x e) envx = AnnLam x $ substIExp e envx
substIExp (IGRef e) envx = GRef $ substIExp e envx
substIExp (IGDeRef e) envx = GDeRef $ substIExp e envx
substIExp (IGAssign e1 e2) envx = GAssign (substIExp e1 envx) $ substIExp e2 envx
substIExp (IC e _) envx = substIExp e envx
