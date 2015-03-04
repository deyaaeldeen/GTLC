{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fwarn-incomplete-patterns #-}

module GTLC.TypeChecker(runTypeCheck, mkCoerceLUD, seqL, isConsistent) where

import Control.Monad.Error
import Control.Monad.Reader
import qualified Data.Map as Map

import GTLC.Syntax

-- | Computes the greatest lower bound with respect to the ordering relation “less or equally dynamic”.
meet :: Type -> Type -> Maybe Type
meet t Dyn = Just t
meet Dyn t = Just t
meet IntTy t@IntTy = Just t
meet BoolTy t@BoolTy = Just t
meet (Fun t11 t12) (Fun t21 t22) = maybe Nothing (\t1 -> maybe Nothing (Just . (Fun t1)) (meet t12 t22)) (meet t11 t21)
meet (GRefTy t1) (GRefTy t2) = maybe Nothing (Just . GRefTy) $ meet t1 t2
meet _ _ = Nothing


-- | Checks if two types are consistent.
isConsistent :: Type -> Type -> Bool
isConsistent t1 t2 = maybe False (const True) (meet t1 t2)


-- | Computes the type of a constant or operator.
typeof :: SExp -> Type
typeof (N _) = IntTy
typeof (B _) = BoolTy
typeof (Op Inc _) = Fun IntTy IntTy
typeof (Op Dec _) = Fun IntTy IntTy
typeof (Op ZeroQ _) = Fun IntTy BoolTy


type CoerceT = Type -> Type -> Coercion

-- | Translates casts to coercions in the lazy downcast approach.
mkCoerceLD :: CoerceT
mkCoerceLD Dyn Dyn = IdC Dyn
mkCoerceLD BoolTy BoolTy = IdC BoolTy
mkCoerceLD IntTy IntTy = IdC IntTy
mkCoerceLD Dyn t = ProjC t
mkCoerceLD t Dyn = InjC t
mkCoerceLD (Fun t1 t2) (Fun t3 t4) = FunC (mkCoerceLD t3 t1) (mkCoerceLD t2 t4)
mkCoerceLD t1 t2 = FailC t1 t2


-- | Translates casts to coercions in the lazy up down cast approach.
mkCoerceLUD :: CoerceT
mkCoerceLUD Dyn Dyn = IdC Dyn
mkCoerceLUD BoolTy BoolTy = IdC BoolTy
mkCoerceLUD IntTy IntTy = IdC IntTy
mkCoerceLUD Dyn IntTy = ProjC IntTy
mkCoerceLUD Dyn BoolTy = ProjC BoolTy
mkCoerceLUD Dyn (Fun t1 t2) = SeqC (ProjC (Fun Dyn Dyn)) (FunC (mkCoerceLUD t1 Dyn) (mkCoerceLUD Dyn t2))
mkCoerceLUD IntTy Dyn = InjC IntTy
mkCoerceLUD BoolTy Dyn = InjC BoolTy
mkCoerceLUD (Fun t1 t2) Dyn = SeqC (FunC (mkCoerceLUD Dyn t1) (mkCoerceLUD t2 Dyn)) (InjC (Fun Dyn Dyn))
mkCoerceLUD (Fun t1 t2) (Fun t3 t4) = FunC (mkCoerceLUD t3 t1) (mkCoerceLUD t2 t4)
mkCoerceLUD (GRefTy t1) (GRefTy t2) = RefC (mkCoerceLUD t2 t1) (mkCoerceLUD t1 t2)
mkCoerceLUD Dyn t@(GRefTy _) = SeqC (mkCoerceLUD Dyn (GRefTy Dyn)) (mkCoerceLUD (GRefTy Dyn) t)
mkCoerceLUD t@(GRefTy _) Dyn = SeqC (mkCoerceLUD t (GRefTy Dyn)) (mkCoerceLUD (GRefTy Dyn) Dyn)
mkCoerceLUD t1 t2 = FailC t1 t2


-- | Coerces an expression from one type to another if they are different.
mkCoerce :: IExp -> Type -> Type -> IExp
mkCoerce e t1 t2 | t1 == t2 = e | otherwise = IC e $ mkCoerceLUD t1 t2


-- | Returns the corresponding source and target type of a coercion.
typeofCoercion :: Coercion -> (Type, Type)
typeofCoercion (IdC t) = (t,t)
typeofCoercion (InjC t) = (t, Dyn)
typeofCoercion (ProjC t) = (Dyn, t)
typeofCoercion (FunC (typeofCoercion -> (t21,t11)) (typeofCoercion -> (t12,t22))) = (Fun t11 t12, Fun t21 t22)
typeofCoercion (SeqC (typeofCoercion -> (t1,t2)) (typeofCoercion -> (t3,t4))) | t2 == t3 = (t1,t3)
typeofCoercion (FailC t1 t2) = (t1,t2)


-- | Composes coercion in lazy fashion.
seqL :: CoerceT -> Coercion -> Coercion -> Coercion
seqL _ (IdC _) c = c
seqL _ c (IdC _) = c
seqL c (InjC t1) (ProjC t2) = c t1 t2
seqL c (FunC c11 c12) (FunC c21 c22) = FunC (seqL c c21 c11) (seqL c c12 c22)
seqL _ f@(FailC _ _) _ = f
seqL _ (InjC _) f@(FailC _ _) = f
seqL _ (FunC _ _) f@(FailC _ _) = f
--seqL c (SeqC c1 c2) c3 = seqL c c1 $ seqL c c2 c3
--seqL c a@(ProjC _) b@(SeqC (FunC _ _) _) = SeqC a b
--seqL c c1 (SeqC c2 c3) = seqL c (seqL c c1 c2) c3
seqL _ c1 c2 = SeqC c1 c2


-- | Type-check expression of the GTLC, converting it to one in intermediate language with explicit casts.
typecheck :: SExp -> TcMonad (IExp,Type)
typecheck e@(N n) = return (IN n, typeof e)
typecheck e@(B b) = return (IB b, typeof e)
typecheck e@(Op op e1) = typecheck e1 >>= \(e1',t) -> let (Fun t1 t2) = typeof e in if (isConsistent t t1) then return (IOp op $ mkCoerce e1' t t1, t2) else throwError $ PrimitiveOperator op t
typecheck (If e e1 e2) = typecheck e >>= \(e',t) -> typecheck e1 >>= \(e1', t1) -> typecheck e2 >>= \(e2', t2) -> if (isConsistent t BoolTy) && (isConsistent t1 t2) then
    case meet t1 t2 of
     Just if_T -> return ((IIf (mkCoerce e' t BoolTy) (mkCoerce e1' t1 if_T) (mkCoerce e2' t2 if_T)), if_T)
     Nothing -> throwError $ IllTypedIfExp "The two arms of the If expression do not have consistent types"
    else
    throwError $ IllTypedIfExp "The condition of the If expression is not consistent with the boolean type"
typecheck (Var x) = lookupTy x >>= \t -> return (IVar x,t)
typecheck (Lam x e) = typecheck $ AnnLam (x,Dyn) e
typecheck (AnnLam v@(_,t1) e) = extendTyCtx v (typecheck e) >>= \(e',t2) -> return (IAnnLam v e', Fun t1 t2)
typecheck (App e1 e2) = typecheck e2 >>= \(e2',t2) -> typecheck e1 >>= \(e1',t1) -> case t1 of
                                                                              Dyn -> return (IApp (mkCoerce e1' Dyn (Fun t2 Dyn)) e2', Dyn)
                                                                              (Fun t11 t12) -> if isConsistent t2 t11 then return (IApp e1' $ mkCoerce e2' t2 t11, t12) else throwError $ ArgParamMismatch t11 t2
                                                                              _ -> throwError CallNonFunction
typecheck (GRef e)  = typecheck e >>= \(e',t) -> return (IGRef e', GRefTy t)
typecheck (GDeRef e) = typecheck e >>= \(e',t) -> case t of
                                                   GRefTy t' -> return (IGDeRef e', t')
                                                   Dyn -> return (IGDeRef $ mkCoerce e' Dyn (GRefTy Dyn), Dyn)
                                                   _ -> throwError $ BadDereference t
typecheck (GAssign e1 e2) = typecheck e1 >>= \(e1',t1) -> case t1 of
                                                           (GRefTy t') -> typecheck e2 >>= \(e2',t2) -> if isConsistent t' t2 then return (IGAssign e1' $ mkCoerce e2' t2 t', t2) else throwError $ IllTypedAssignment t' t2
                                                           Dyn -> typecheck e2 >>= \(e2',t2) -> return (IGAssign (mkCoerce e1' Dyn (GRefTy Dyn)) $ mkCoerce e2' t2 Dyn, Dyn)
                                                           _ -> throwError $ BadAssignment t1
typecheck (Let var e1 e2) = typecheck e1 >>= \(e1',t1) -> extendTyCtx (var,t1) $ typecheck e2 >>= \(e2',t2) -> return (ILet var e1' e2', t2)
typecheck _ = throwError $ UnknownTyError "Unknown Error!"


runTcMonad :: TcMonad a -> TyGamma -> IO (Either TyErr a)
runTcMonad m = runErrorT . (runReaderT m)


runTypeCheck :: SExp -> IO (Either TyErr (IExp, Type))
runTypeCheck e = runTcMonad (typecheck e) (TyGamma {tyCtx = Map.empty})
