module Syntax where

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
  | VLam (Value -> Value)
  | VCast BlameLabel Value Type Type
  | Blame BlameLabel

data Type =
  Dyn
  | IntTy
  | BoolTy
  | Fun Type Type
  deriving (Show,Eq,Read)

type BlameLabel = String

type Name = String


expToVal :: Exp -> Value
expToVal (N x) = (VN x)
expToVal (B x) = (VB x)
expToVal _ = undefined

valToExp :: Value -> Exp
valToExp (VN x) = (N x)
valToExp (VB x) = (B x)
valToExp _ = undefined
