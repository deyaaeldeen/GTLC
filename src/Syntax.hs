{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Syntax where

import Text.Show.Functions
import Control.Monad.Error
import Control.Monad.Reader
import qualified Data.Map as Map


type EvMonad = ReaderT Env (ErrorT EvErr IO)

data Env = Env { env :: Map.Map Name Value }


data EvErr =
  EvUnknownError String
  | EvUndefinedVar Name
  | EvCallNonFunctionNonCast
  deriving (Eq)


instance Error EvErr where
  strMsg msg = EvUnknownError msg


instance Show EvErr where
  show (EvUndefinedVar v) = "The variable " ++ show v ++ " is not bounded"
  show (EvUnknownError s) = s
  show EvCallNonFunctionNonCast = "The expression in the function position is neither a function nor a cast of one"

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

data Value =
  VN Int
  | VB Bool
  | VLam (Value -> EvMonad Value) Exp
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


expToVal :: Exp -> Value
expToVal (N x) = (VN x)
expToVal (B x) = (VB x)
expToVal (ICast e l t1 t2) = (VCast l (expToVal e) t1 t2)
expToVal _ = undefined

valToExp :: Value -> Exp
valToExp (VN x) = (N x)
valToExp (VB x) = (B x)
valToExp (VLam _ e) = e
valToExp (VCast l e t1 t2) = Cast (valToExp e) l t2
valToExp _ = undefined
