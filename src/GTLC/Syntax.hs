{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module GTLC.Syntax where

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
  | VLam (Value -> EvMonad Value) Exp -- closure and syntactic representation
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


intermediate2surface :: Exp -> Exp
intermediate2surface (IIf e1 e2 e3) = (If (intermediate2surface e1) (intermediate2surface e2) (intermediate2surface e3) "")
intermediate2surface (ICast e l t1 t2) = intermediate2surface e
intermediate2surface (IApp e1 e2) = App (intermediate2surface e1) (intermediate2surface e2) ""
intermediate2surface (IOp op e) = Op op (intermediate2surface e) ""
intermediate2surface (AnnLam v e) = AnnLam v (intermediate2surface e)
intermediate2surface e = e

valToExp :: Value -> Exp
valToExp (VN x) = (N x)
valToExp (VB x) = (B x)
valToExp (VLam _ e) = intermediate2surface e
valToExp (VCast l e t1 t2) = Cast (valToExp e) l t2
