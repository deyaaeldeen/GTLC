{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module GTLC.Syntax where

import Control.Monad.Error
import Control.Monad.Reader
import qualified Data.Map as Map


type EvMonad = ReaderT Env (ErrorT EvErr IO)

data Env = Env { env :: Map.Map Name Value} deriving Show


data EvErr =
  EvUnknownError String
  | EvUndefinedVar Name
  | EvCallNonFunctionNonCast
  deriving (Eq)


instance Error EvErr where
  strMsg msg = EvUnknownError msg


instance Show EvErr where
  show (EvUndefinedVar v) = "The variable " ++ show v ++ " is not bound"
  show (EvUnknownError s) = s
  show EvCallNonFunctionNonCast = "The expression in the function position is neither a function nor a cast of one"

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
    --Intermediate language
  | IOp Operator Exp
  | ICast Exp BlameLabel Type Type
  | IApp Exp Exp
  | IIf Exp Exp Exp
  deriving (Show,Eq,Read)

data Value =
  VN Int
  | VB Bool
  | Closure (Name,Type) Exp Env
  | VCast BlameLabel Value Type Type
  | VBlame BlameLabel
  deriving (Show)

data Type =
  Dyn
  | IntTy
  | BoolTy
  | Fun Type Type
  deriving (Show,Eq,Read)

data Observable =
  ON Int
  | OB Bool
  | Function
  | Dynamic
  | OBlame String
  deriving (Show,Eq)

type BlameLabel = String

type Name = String


-- | Translates values to expressions.
valToExp :: Value -> Exp
valToExp (VN x) = (N x)
valToExp (VB x) = (B x)
valToExp (Closure p@(x,t) e envx) = AnnLam p $ substExp e envx
valToExp (VCast l e t1 t2) = Cast (valToExp e) l t2


-- | Substitutes variables with values in the environment and translates from the intermediate language to the surface language.
substExp :: Exp -> Env -> Exp
substExp (Op op e l) envx = Op op (substExp e envx) l
substExp (If e1 e2 e3 l) envx = If (substExp e1 envx) (substExp e2 envx) (substExp e3 envx) l
substExp (App e1 e2 l) envx = App (substExp e1 envx) (substExp e2 envx) l
substExp (Cast e l t) envx = Cast (substExp e envx) l t
substExp (IOp op e) envx = Op op (substExp e envx) ""
substExp (IIf e1 e2 e3) envx = If (substExp e1 envx) (substExp e2 envx) (substExp e3 envx) ""
substExp v@(Var x) (Env envx) = case Map.lookup x envx of
                          Just e -> valToExp e
                          Nothing -> v
substExp (IApp e1 e2) envx = App (substExp e1 envx) (substExp e2 envx) ""
substExp (AnnLam x e) envx = AnnLam x (substExp e envx)
substExp (ICast e _ _ _) envx = substExp e envx
substExp e _ = e
