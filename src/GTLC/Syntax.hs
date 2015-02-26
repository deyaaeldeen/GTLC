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
  deriving (Eq)


instance Error EvErr where
  strMsg msg = EvUnknownError msg


instance Show EvErr where
  show (EvUndefinedVar v) = "The variable " ++ show v ++ " is not bound"
  show (EvUnknownError s) = s
  show EvCallNonFunctionNonCast = "The expression in the function position is neither a function nor a cast of one"
  show EvBadReference = "The expression in the reference position is not a reference"
  show EvBadLocation = "Trying to access unallocated memory location"

data Operator = Inc | Dec | ZeroQ deriving (Show,Eq,Read)

data Exp =
  -- Surface language
  N Int
  | B Bool
  | Op Operator Exp BlameLabel
  | If Exp Exp Exp BlameLabel 
  | Var Name
  | App Exp Exp BlameLabel
  | Lam Name Exp
  | AnnLam (Name,Type) Exp
  | Cast Exp BlameLabel Type
  | GRef Exp
  | GDeRef Exp BlameLabel
  | GAssign Exp Exp BlameLabel
    --Intermediate language
  | IOp Operator Exp
  | ICast Exp BlameLabel Type Type
  | IApp Exp Exp
  | IIf Exp Exp Exp
  | IGRef Exp
  | IGDeRef Exp
  | IGAssign Exp Exp
  deriving (Show,Eq,Read)

data Value =
  VN Int
  | VB Bool
  | Closure (Name,Type) Exp Env
  | VCast Value BlameLabel Type Type
  | VBlame BlameLabel
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
  | InjC Type
  | ProjC Type BlameLabel
  | FunC Coercion Coercion
  | SeqC Coercion Coercion
  | FailC BlameLabel Type Type
  | CGRef Coercion Coercion


type BlameLabel = String

type Name = String


-- | Translates values to expressions.
valToExp :: Value -> Exp
valToExp (VN x) = (N x)
valToExp (VB x) = (B x)
valToExp (Closure p@(x,t) e envx) = AnnLam p $ substExp e envx
valToExp (VCast e l t1 t2) = Cast (valToExp e) l t2


-- | Substitutes variables with values in the environment and translates from the intermediate language to the surface language.
substExp :: Exp -> Env -> Exp
substExp (Op op e l) envx = Op op (substExp e envx) l
substExp (If e1 e2 e3 l) envx = If (substExp e1 envx) (substExp e2 envx) (substExp e3 envx) l
substExp (App e1 e2 l) envx = App (substExp e1 envx) (substExp e2 envx) l
substExp (Cast e l t) envx = Cast (substExp e envx) l t
substExp (IOp op e) envx = Op op (substExp e envx) ""
substExp (IIf e1 e2 e3) envx = If (substExp e1 envx) (substExp e2 envx) (substExp e3 envx) ""
substExp v@(Var x) (Env envx) = maybe v valToExp (M.lookup x envx)
substExp (IApp e1 e2) envx = App (substExp e1 envx) (substExp e2 envx) ""
substExp (AnnLam x e) envx = AnnLam x (substExp e envx)
substExp (ICast e _ _ _) envx = substExp e envx
substExp e _ = e
