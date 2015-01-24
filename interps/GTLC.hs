module GTLC where

--import Control.Monad.Error

data BasicType = Nat | Boolean deriving (Show,Eq,Read)
data Type = B BasicType | Fun Type Type | Dyn deriving (Show,Eq,Read)
data Constant = N Int | T | F deriving (Show,Eq,Read)
data Operator = Inc | Dec | ZeroQ deriving (Show,Eq,Read)
type BlameLabel = String
type Var = String
data Expression
    = C Constant 
    | Op Operator Expression BlameLabel 
    | If Expression Expression Expression BlameLabel 
    | V Var
    | App Expression Expression BlameLabel
    | Lam Var Expression
    | TLam Var Type Expression
    | Cast Expression BlameLabel Type
      --Intermediate language
    | IOp Operator Expression
    | ICast Expression BlameLabel Type Type
    | IApp Expression Expression
    | IIf Expression Expression Expression
    deriving (Show,Eq,Read)

meet :: Type -> Type -> Maybe Type
meet t Dyn = Just t
meet Dyn t = Just t
meet (B Nat) t@(B Nat) = Just t
meet (B Boolean) t@(B Boolean) = Just t
meet (Fun t11 t12) (Fun t21 t22) = case (meet t11 t21) of
                                    Just t1 -> case (meet t12 t22) of
                                               Just t2 -> Just (Fun t1 t2)
                                               _ -> Nothing
                                    _ -> Nothing
meet _ _ = Nothing


consistentQ :: Type -> Type -> Bool
consistentQ t1 t2 = maybe False (\_ -> True) (meet t1 t2)

typeof :: (Either Constant Operator) -> Type
typeof (Left (N _)) = B Nat
typeof (Left T) = B Boolean
typeof (Left F) = B Boolean
typeof (Right Inc) = Fun (B Nat) (B Nat)
typeof (Right Dec) = Fun (B Nat) (B Nat)
typeof (Right ZeroQ) = Fun (B Nat) (B Boolean)

mk_cast :: BlameLabel -> Expression -> Type -> Type -> Expression
mk_cast l e t1 t2 = if t1 == t2 then e else (ICast e l t1 t2)

type Env = [(Var,Type)]

data TypeError = PrimitiveOperator
                 | IllTypedIfExpression
                 | ArgParamMismatch
                 | CallNonFunction
                 | UndefinedVar
                   deriving (Show,Eq,Read)

data CastError = CastBetweenInconsistentTypes

type Error = Either TypeError CastError

-- | Type-check expression of the GTLC, converting it to one in intermediate language with explicit casts
typecheck :: Expression -> Env -> Either Error (Expression,Type)
typecheck e@(C c) _ = Right (e, (typeof (Left c)))
typecheck (Op op e l) env = let (Right (e2, t)) = typecheck e env
                                (Fun t1 t2) = typeof (Right op)
                            in if (consistentQ t t1) then Right ((IOp op (mk_cast l e2 t t1)), t2) else Left (Left PrimitiveOperator)
typecheck (If e e1 e2 l) env = let (Right (te, t1)) = typecheck e env
                                   (Right (te1, t2)) = typecheck e1 env
                                   (Right (te2, t3)) = typecheck e2 env
                               in if (consistentQ t1 (B Boolean)) && (consistentQ t2 t3) then
                                    case (meet t2 t3) of
                                     Just if_T -> Right ((IIf (mk_cast l te t1 (B Boolean)) (mk_cast l te1 t2 if_T) (mk_cast l te2 t3 if_T)), if_T)
                                     Nothing -> Left (Left IllTypedIfExpression)
                                  else
                                    Left (Left IllTypedIfExpression)
typecheck e@(V x) env = case lookup x env of
                         Just t -> Right (e,t)
                         Nothing -> Left (Left UndefinedVar)
typecheck (Lam x e) env = typecheck (TLam x Dyn e) env
typecheck (TLam x t e) env = case (typecheck e ((x,t):env)) of
                                Right (e1,t1) -> Right ((TLam x t e1),(Fun t t1))
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

