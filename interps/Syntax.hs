module Syntax where

import Test.QuickCheck

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
