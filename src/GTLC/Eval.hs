{-# LANGUAGE NamedFieldPuns, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module GTLC.Eval(interpLD) where

import Control.Monad.Error
import Control.Monad.Reader
import qualified Data.Map as Map

import GTLC.Syntax

-- debugging imports
import Debug.Trace
import GTLC.TypeChecker


-- | Look for the value of a variable in the environment
-- throwing an error if the name doesn't exist.
lookupVal :: (MonadReader Env m, MonadError EvErr m) => Name -> m Value
lookupVal v = asks env >>= \env -> maybe (throwError (EvUndefinedVar v)) return (Map.lookup v env)


-- | Extend the environment with a new binding.
extendEnv :: (MonadReader Env m) => (Name, Value) -> Env -> m a -> m a
extendEnv (x,v) m@(Env {env = en}) = local (\_ -> m { env = Map.insert x v en })


-- | Defines shallow consistency relation that we use to determine whether to report cast error.
shallowConsistentQ :: Type -> Type -> Bool
shallowConsistentQ Dyn t = True
shallowConsistentQ t Dyn = True
shallowConsistentQ BoolTy BoolTy = True
shallowConsistentQ IntTy IntTy = True
shallowConsistentQ (Fun _ _) (Fun _ _) = True
shallowConsistentQ _ _ = False


-- | Wraps a run-time cast around a value if the two types are different.
mkCast :: BlameLabel -> Value -> Type -> Type -> Value
mkCast l v t1 t2 = if t1 == t2 then v else (VCast l v t1 t2)


-- | Performs run-time cast on a value using downcast approach.
applyCastLD :: BlameLabel -> Value -> Type -> Type -> Value
applyCastLD l v t1 t2 = if shallowConsistentQ t1 t2
                        then
                          case t1 of
                          Dyn -> case v of
                            (VCast l2 v2 t3 Dyn) -> applyCastLD l v2 t3 t2
                            _ -> mkCast l v t1 t2
                          _ -> mkCast l v t1 t2
                        else
                          VBlame l


-- | Performs function application.
applyLazy :: Value -> Value -> EvMonad Value
applyLazy (VCast l v (Fun t1 t2) (Fun t3 t4)) v2 = applyLazy v (applyCastLD l v2 t3 t1) >>= \x -> return $ applyCastLD l x t2 t4
applyLazy (Closure (x,_) e env) v = extendEnv (x,v) env (interp applyCastLD applyLazy e)
applyLazy _ _ = throwError EvCallNonFunctionNonCast

-- The problem is I substitute at different places, so one solution is to keep track of all bound variables and substitute them at the end
-- | Interprets the intermediate language.
-- Not defined on the surface language
interp :: (BlameLabel -> Value -> Type -> Type -> Value) -> (Value -> Value -> EvMonad Value) -> Exp -> EvMonad Value
interp _ _ (N x) = return (VN x)
interp _ _ (B x) = return (VB x)
interp appcast applazy (IOp Inc e) = interp appcast applazy e >>= \(VN v) -> return $ VN(v+1)
interp appcast applazy (IOp Dec e) = interp appcast applazy e >>= \(VN v) -> return $ VN(v-1)
interp appcast applazy (IOp ZeroQ e) = interp appcast applazy e >>= \(VN v) -> return $ VB(v == 0)
interp appcast applazy (IIf e1 e2 e3) = interp appcast applazy e1 >>= \(VB v) -> if v then interp appcast applazy e2 else interp appcast applazy e3
interp _ _ (Var v) = lookupVal v
interp appcast applazy (IApp e1 e2) = interp appcast applazy e1 >>= \f -> interp appcast applazy e2 >>= applazy f
interp appcast applazy (AnnLam x e) = ask >>= return . (Closure x e)
interp appcast applazy (ICast e l t1 t2) = (interp appcast applazy e) >>= \v -> return $ appcast l v t1 t2


-- | Interpreter for the intermediate language with lazy down casts
interpLD :: Exp -> IO (Either EvErr Value)
interpLD e = runErrorT $ runReaderT (interp applyCastLD applyLazy e) (Env {env = Map.empty})


-- | Turns the evaluation result to an observable.
observeLazy :: Value -> Observable
observeLazy (VN x) = (ON x)
observeLazy (VB x) = (OB x)
observeLazy (Closure _ _ _) = Function
observeLazy (VCast _ _ _ (Fun _ _)) = Function
observeLazy (VCast _ _ _ Dyn) = Dynamic
observeLazy (VBlame l) = (OBlame l)
