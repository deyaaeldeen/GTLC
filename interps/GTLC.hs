module GTLC where

data BasicType = Int | Boolean deriving (Show,Eq,Read)
data Type = B BasicType | Fun Type Type | Dyn deriving (Show,Eq,Read)
data Constant = N BasicType | T | F deriving (Show,Eq,Read)
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

consistentQ :: Type -> Type -> Bool
consistentQ _ Dyn = True
consistentQ Dyn _ = True
consistentQ (B Int) (B Int) = True
consistentQ (B Boolean) (B Boolean) = True
consistentQ (Fun t11 t12) (Fun t21 t22) = (consistentQ t11 t21) && (consistentQ t12 t22)
consistentQ _ _ = False

meet :: Type -> Type -> Maybe Type
meet t Dyn = Just t
meet Dyn t = Just t
meet (B Int) t@(B Int) = Just t
meet (B Boolean) t@(B Boolean) = Just t
meet (Fun t11 t12) (Fun t21 t22) = case (meet t11 t21) of
                                    Just t1 -> case (meet t12 t22) of
                                               Just t2 -> Just (Fun t1 t2)
                                               _ -> Nothing
                                    _ -> Nothing
meet _ _ = Nothing

typeof :: (Either Constant Operator) -> Type
typeof (Left (N _)) = B Int
typeof (Left T) = B Boolean
typeof (Left F) = B Boolean
typeof (Right Inc) = Fun (B Int) (B Int)
typeof (Right Dec) = Fun (B Int) (B Int)
typeof (Right ZeroQ) = Fun (B Int) (B Boolean)

mk_cast :: BlameLabel -> Expression -> Type -> Type -> Expression
mk_cast l e t1 t2 = if t1 == t2 then e else (ICast e l t1 t2)

type Env = [(Var,Type)]
data TypeError = PrimitiveOperator
                 | IllTypedIfExpression
                 | CastBetweenInconsistentTypes
                 | ArgParamMismatch
                 | CallNonFunction
                 | UndefinedVar
                   deriving (Show,Eq,Read)

-- Typechecker and cast insertion (converting to the intermediate language)
typecheck :: Expression -> Env -> Either TypeError (Expression,Type)
typecheck e@(C c) env = Right (e, (typeof (Left c)))
typecheck (Op op e l) env = let (Right (e2, t)) = typecheck e env
                                (Fun t1 t2) = typeof (Right op)
                            in if (consistentQ t t1) then Right ((IOp op (mk_cast l e2 t t1)), t2) else Left PrimitiveOperator
typecheck (If e e1 e2 l) env = let (Right (te, t1)) = typecheck e env
                                   (Right (te1, t2)) = typecheck e1 env
                                   (Right (te2, t3)) = typecheck e2 env
                               in if (consistentQ t1 (B Boolean)) && (consistentQ t2 t3) then
                                    case (meet t2 t3) of
                                     Just if_T -> Right ((IIf (mk_cast l e t1 (B Boolean)) (mk_cast l e1 t2 if_T) (mk_cast l e2 t3 if_T)), if_T)
                                     Nothing -> Left IllTypedIfExpression
                                  else
                                    Left IllTypedIfExpression
typecheck e@(V x) env = case lookup x env of
                         Just t -> Right (e,t)
                         Nothing -> Left UndefinedVar
typecheck (Lam x e) env = typecheck (TLam x Dyn e) env
typecheck (TLam x t e) env = case (typecheck e ((x,t):env)) of
                                Right (e1,t1) -> Right ((TLam x t e1),(Fun t t1))
                                e -> e
typecheck (Cast e l t) env = case (typecheck e env) of
                          Right (e2,t2) -> if (consistentQ t2 t) then Right ((mk_cast l e2 t2 t),t) else Left CastBetweenInconsistentTypes
                          e -> e
typecheck (App e1 e2 l) env = case (typecheck e2 env) of
                               Right (e4,t) -> case (typecheck e1 env) of
                                                Right (e3, Dyn) -> Right ((IApp (mk_cast l e3 Dyn (Fun t Dyn)) e4),Dyn)
                                                Right (e3, (Fun t21 t22)) -> if (consistentQ t t21) then Right ((IApp e3 (mk_cast l e4 t (Fun t t21))), Dyn) else Left ArgParamMismatch
                                                Right (e3, t2) -> Left CallNonFunction
                                                e -> e
                               e -> e
