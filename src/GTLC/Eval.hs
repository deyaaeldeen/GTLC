{-# LANGUAGE NamedFieldPuns, FlexibleContexts, ViewPatterns #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module GTLC.Eval(interpLD, interpLUD) where

import Control.Monad.Error
import Control.Monad.Reader
import qualified Data.Map as Map

import GTLC.Syntax
import GTLC.TypeChecker


-- | Look for the value of a variable in the environment
-- throwing an error if the name doesn't exist.
lookupVal :: (MonadReader Env m, MonadError EvErr m) => Name -> m Value
lookupVal v = asks env >>= \env -> maybe (throwError (EvUndefinedVar v)) return (Map.lookup v env)


-- | Extend the environment with a new binding.
extendEnv :: (MonadReader Env m) => (Name, Value) -> Env -> m a -> m a
extendEnv (x,v) m@(Env {env = en}) = local (\_ -> m { env = Map.insert x v en })


-- | Defines shallow consistency relation that we use to determine whether to report cast error.
isShallowConsistent :: Type -> Type -> Bool
isShallowConsistent Dyn t = True
isShallowConsistent t Dyn = True
isShallowConsistent BoolTy BoolTy = True
isShallowConsistent IntTy IntTy = True
isShallowConsistent (Fun _ _) (Fun _ _) = True
isShallowConsistent _ _ = False


-- | Wraps a run-time cast around a value if the two types are different.
mkCast :: BlameLabel -> Value -> Type -> Type -> Value
mkCast l v t1 t2 | t1 == t2 = v | otherwise = VCast v l t1 t2


type CastT = BlameLabel -> Value -> Type -> Type -> Value
type AppT = Value -> Value -> EvMonad Value


-- | Performs run-time cast on a value in the downcast approach.
applyCastLD :: CastT
applyCastLD l v t1 t2 = if isShallowConsistent t1 t2 then
                          case (t1,v) of
                           (Dyn, VCast v2 l2 t3 Dyn) -> applyCastLD l v2 t3 t2
                           _ -> mkCast l v t1 t2
                        else VBlame l


-- | Performs run-time cast on a value in the downcast approach.
applyCastLUD :: CastT
applyCastLUD l v t1 t2 = if isShallowConsistent t1 t2 then
                           case (t1,t2,v) of
                            (Dyn, t, VCast v2 l2 t3 Dyn) -> applyCastLD l v2 t3 t2
                            (Fun Dyn Dyn, Dyn, _) -> VCast v l (Fun Dyn Dyn) Dyn
                            (Fun t11 t12, Dyn, _) -> VCast (VCast v l (Fun t11 t12) (Fun Dyn Dyn)) l (Fun Dyn Dyn) Dyn
                            _ -> mkCast l v t1 t2
                         else VBlame l


-- | Performs function application.
applyLazy :: CastT -> AppT
applyLazy cast (VCast v l (Fun t1 t2) (Fun t3 t4)) v2 = applyLazy cast v (cast l v2 t3 t1) >>= \x -> return $ cast l x t2 t4
applyLazy cast (Closure (x,_) e env) v = extendEnv (x,v) env (interp cast (applyLazy cast) e)
applyLazy _ _ _ = throwError EvCallNonFunctionNonCast


-- | Interprets the intermediate language.
-- Not defined on the surface language
interp :: CastT -> AppT -> Exp -> EvMonad Value
interp _ _ (N x) = return (VN x)
interp _ _ (B x) = return (VB x)
interp cast app (IOp Inc e) = interp cast app e >>= \(VN v) -> return $ VN(v+1)
interp cast app (IOp Dec e) = interp cast app e >>= \(VN v) -> return $ VN(v-1)
interp cast app (IOp ZeroQ e) = interp cast app e >>= \(VN v) -> return $ VB(v == 0)
interp cast app (IIf e1 e2 e3) = interp cast app e1 >>= \(VB v) -> if v then interp cast app e2 else interp cast app e3
interp _ _ (Var v) = lookupVal v
interp cast app (IApp e1 e2) = interp cast app e1 >>= \f -> interp cast app e2 >>= app f
interp cast app (AnnLam x e) = ask >>= return . (Closure x e)
interp cast app (ICast e l t1 t2) = (interp cast app e) >>= \v -> return $ cast l v t1 t2


-- | Interpreter for the intermediate language with lazy down casts.
interpLD :: Exp -> IO (Either EvErr Value)
interpLD e = runErrorT $ runReaderT (interp applyCastLD (applyLazy applyCastLD) e) (Env {env = Map.empty})


-- | Interpreter for the intermediate language with lazy up down casts.
interpLUD :: Exp -> IO (Either EvErr Value)
interpLUD e = runErrorT $ runReaderT (interp applyCastLUD (applyLazy applyCastLUD) e) (Env {env = Map.empty})


-- | Returns the corresponding source and target type of a coercion.
typeofCoercion :: Coercion -> (Type, Type)
typeofCoercion (IdC t) = (t,t)
typeofCoercion (InjC t) = (t, Dyn)
typeofCoercion (ProjC t _) = (Dyn, t)
typeofCoercion (FunC (typeofCoercion -> (t21,t11)) (typeofCoercion -> (t12,t22))) = (Fun t11 t12, Fun t21 t22)
typeofCoercion (SeqC (typeofCoercion -> (t1,t2)) (typeofCoercion -> (t3,t4))) | t2 == t3 = (t1,t3)
typeofCoercion (FailC _ t1 t2) = (t1,t2)


type CoerceT = Type -> Type -> BlameLabel -> Coercion

-- | Translates casts to coercions in the lazy downcast approach.
mkCoerceLD :: CoerceT
mkCoerceLD Dyn Dyn _ = IdC Dyn
mkCoerceLD BoolTy BoolTy _ = IdC BoolTy
mkCoerceLD IntTy IntTy _ = IdC IntTy
mkCoerceLD Dyn t l = ProjC t l
mkCoerceLD t Dyn _ = InjC t
mkCoerceLD (Fun t1 t2) (Fun t3 t4) l = FunC (mkCoerceLD t3 t1 l) (mkCoerceLD t2 t4 l)
mkCoerceLD t1 t2 l = FailC l t1 t2


-- | Translates casts to coercions in the lazy up down cast approach.
mkCoerceLUD :: CoerceT
mkCoerceLUD Dyn Dyn _ = IdC Dyn
mkCoerceLUD BoolTy BoolTy _ = IdC BoolTy
mkCoerceLUD IntTy IntTy _ = IdC IntTy
mkCoerceLUD Dyn IntTy l = ProjC IntTy l
mkCoerceLUD Dyn BoolTy l = ProjC BoolTy l
mkCoerceLUD Dyn (Fun t1 t2) l = SeqC (ProjC (Fun Dyn Dyn) l) (FunC (mkCoerceLUD t1 Dyn l) (mkCoerceLUD Dyn t2 l))
mkCoerceLUD IntTy Dyn _ = InjC IntTy
mkCoerceLUD BoolTy Dyn _ = InjC BoolTy
mkCoerceLUD (Fun t1 t2) Dyn l = SeqC (FunC (mkCoerceLUD Dyn t1 l) (mkCoerceLUD t2 Dyn l)) (InjC (Fun Dyn Dyn))
mkCoerceLUD (Fun t1 t2) (Fun t3 t4) l = FunC (mkCoerceLUD t3 t1 l) (mkCoerceLUD t2 t4 l)
mkCoerceLUD t1 t2 l = FailC l t1 t2


-- | Composes coercion in lazy fashion.
seqL :: CoerceT -> Coercion -> Coercion -> Coercion
seqL _ (IdC _) c = c
seqL _ c (IdC _) = c
seqL c (InjC t1) (ProjC t2 l) = c t1 t2 l
seqL c (FunC c11 c12) (FunC c21 c22) = FunC (seqL c c21 c11) (seqL c c12 c22)
seqL c f@(FailC l t1 t2) _ = f
seqL c (InjC _) f@(FailC l t1 t2) = f
seqL c (FunC _ _) f@(FailC l t1 t2) = f
seqL c (SeqC c1 c2) c3 = seqL c c1 $ seqL c c2 c3
seqL c a@(ProjC t l) b@(SeqC (FunC c1 c2) c3) = SeqC a b
seqL c c1 (SeqC c2 c3) = seqL c (seqL c c1 c2) c3
seqL _ c1 c2 = SeqC c1 c2
