module GTLC where

--import Control.Monad.Error

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
  Dyn -- Dyn can be represented by Nothing constructor of Maybe monad but I chose not to for better readability
  | IntTy
  | BoolTy
  | Fun Type Type
  deriving (Show,Eq,Read)

type BlameLabel = String
type Name = String

-- | Computes the greatest lower bound with respect to the ordering relation “less or equally dynamic”
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


-- | Checks if two types are consistent
consistentQ :: Type -> Type -> Bool
consistentQ t1 t2 = maybe False (\_ -> True) (meet t1 t2)


-- | Computes the type of a constant or operator
typeof :: Exp -> Type
typeof (N _) = IntTy
typeof (B _) = BoolTy
typeof (Op Inc _ _) = Fun IntTy IntTy
typeof (Op Dec _ _) = Fun IntTy IntTy
typeof (Op ZeroQ _ _) = Fun IntTy BoolTy
typeof _ = undefined


-- | Wraps a run-time cast around the expression if the two types are different
mk_cast :: BlameLabel -> Exp -> Type -> Type -> Exp
mk_cast l e t1 t2 = if t1 == t2 then e else (ICast e l t1 t2)

type Env = [(Name,Type)]
data Env2 = Env2 { ctx :: [(Name,Type)],
               -- ^ elaborated term and datatype declarations.
                 globals :: Int
               -- ^ how long the tail of "global" variables in the context is
               --    (used to supress printing those in error messages)
               }

data TypeError = PrimitiveOperator
                 | IllTypedIfExp
                 | ArgParamMismatch
                 | CallNonFunction
                 | UndefinedVar
                   deriving (Show,Eq,Read)

data CastError = CastBetweenInconsistentTypes

type Error = Either TypeError CastError

-- | Type-check expression of the GTLC, converting it to one in intermediate language with explicit casts
typecheck :: Exp -> Env -> Either Error (Exp,Type)
typecheck e@(N _) _ = Right (e, (typeof e))
typecheck e@(B _) _ = Right (e, (typeof e))
typecheck e@(Op op e1 l) env = let (Right (e2, t)) = typecheck e1 env
                                   (Fun t1 t2) = typeof e
                               in if (consistentQ t t1) then Right ((IOp op (mk_cast l e2 t t1)), t2) else Left (Left PrimitiveOperator)
typecheck (If e e1 e2 l) env = let (Right (te, t1)) = typecheck e env
                                   (Right (te1, t2)) = typecheck e1 env
                                   (Right (te2, t3)) = typecheck e2 env
                               in if (consistentQ t1 BoolTy) && (consistentQ t2 t3) then
                                    case (meet t2 t3) of
                                     Just if_T -> Right ((IIf (mk_cast l te t1 BoolTy) (mk_cast l te1 t2 if_T) (mk_cast l te2 t3 if_T)), if_T)
                                     Nothing -> Left (Left IllTypedIfExp)
                                  else
                                    Left (Left IllTypedIfExp)
typecheck e@(Var x) env = case (lookup x env) of
                         Just t -> Right (e,t)
                         Nothing -> Left (Left UndefinedVar)
typecheck (Lam x e) env = typecheck (AnnLam (x,Dyn) e) env
typecheck (AnnLam (x,t) e) env = case (typecheck e ((x,t):env)) of
                                Right (e1,t1) -> Right ((AnnLam (x,t) e1),(Fun t t1))
                                err -> err
typecheck (Cast e l t) env = case (typecheck e env) of
                          Right (e2,t2) -> if (consistentQ t2 t) then Right ((mk_cast l e2 t2 t),t) else Left (Right CastBetweenInconsistentTypes)
                          err -> err
typecheck (App e1 e2 l) env = case (typecheck e2 env) of
                               Right (e4,t) -> case (typecheck e1 env) of
                                                Right (e3, Dyn) -> Right ((IApp (mk_cast l e3 Dyn (Fun t Dyn)) e4),Dyn)
                                                Right (e3, (Fun t21 t22)) -> if (consistentQ t t21) then Right ((IApp e3 (mk_cast l e4 t (Fun t t21))), t22) else Left (Left ArgParamMismatch)
                                                Right _ -> Left (Left CallNonFunction)
                                                err -> err
                               err -> err
typecheck _ _ = undefined

