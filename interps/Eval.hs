{-# LANGUAGE NamedFieldPuns, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Eval(interpLD) where

import Control.Monad.Error
import Control.Monad.Reader
import qualified Data.Map as Map

import Syntax
import TypeChecker


-- | Look for the value of a variable in the environment
-- throwing an error if the name doesn't exist.
lookupVal :: (MonadReader Env m, MonadError EvErr m) => Name -> m Value
lookupVal v = asks env >>= \env -> maybe (throwError (EvUndefinedVar v)) return (Map.lookup v env)


-- | Extend the context with a new binding.
extendEnv :: (MonadReader Env m) => (Name, Value) -> m a -> m a
extendEnv (x,v) = local (\ m@(Env {env = en}) -> m { env = Map.insert x v en })


-- | Defines shallow consistency relation that we use to determine whether to report cast error.
shallowConsistentQ :: Type -> Type -> Bool
shallowConsistentQ Dyn t = True
shallowConsistentQ t Dyn = True
shallowConsistentQ BoolTy BoolTy = True
shallowConsistentQ IntTy IntTy = True
shallowConsistentQ (Fun _ _) (Fun _ _) = True
shallowConsistentQ _ _ = False


-- | Performs run-time cast on a value using downcast approach.
applyCastLD :: BlameLabel -> Value -> Type -> Type -> Value
applyCastLD l v t1 t2 = if shallowConsistentQ t1 t2
                        then
                          case t1 of
                          Dyn -> case v of
                            (VCast l2 v2 t3 Dyn) -> applyCastLD l v t3 t2
                            _ -> expToVal $ mkCast l (valToExp v) t1 t2
                          _ -> expToVal $ mkCast l (valToExp v) t1 t2
                        else
                          VBlame l


-- | Performs function application.
applyLazy :: Value -> Value -> EvMonad Value
applyLazy (VCast l v (Fun t1 t2) (Fun t3 t4)) v2 = applyLazy v (applyCastLD l v2 t3 t1) >>= \x -> return $ applyCastLD l x t2 t4
applyLazy (VLam f _) v = f v
applyLazy _ _ = throwError EvCallNonFunctionNonCast


-- | Turns the evaluation result to an observable.
observeLazy :: Value -> Observable
observeLazy (VN x) = (ON x)
observeLazy (VB x) = (OB x)
observeLazy (VLam _ _) = Function
observeLazy (VCast _ _ _ (Fun _ _)) = Function
observeLazy (VCast _ _ _ Dyn) = Dynamic
observeLazy (VBlame l) = (OBlame l)
observeLazy _ = undefined -- not defined for other casts


-- | Interprets the intermediate language
interp :: (BlameLabel -> Value -> Type -> Type -> Value) -> (Value -> Value -> EvMonad Value) -> Exp -> EvMonad Value
interp _ _ (N x) = return (VN x)
interp _ _ (B x) = return (VB x)
interp appcast applazy (IOp Inc e) = interp appcast applazy e >>= \(VN v) -> return $ VN(v+1)
interp appcast applazy (IOp Dec e) = interp appcast applazy e >>= \(VN v) -> return $ VN(v-1)
interp appcast applazy (IOp ZeroQ e) = interp appcast applazy e >>= \(VN v) -> return $ VB(v == 0)
interp appcast applazy (IIf e1 e2 e3) = interp appcast applazy e1 >>= \(VB v) -> if v then interp appcast applazy e2 else interp appcast applazy e3
interp _ _ (Var v) = lookupVal v
interp appcast applazy (IApp e1 e2) = interp appcast applazy e1 >>= \(VLam f _) -> interp appcast applazy e2 >>= \v -> f v
interp appcast applazy f@(AnnLam (x,_) e) = return $ VLam (\v -> extendEnv (x,v) (interp appcast applazy e)) f
interp appcast applazy (ICast e l t1 t2) = (interp appcast applazy e) >>= \v -> return $ VCast l v t1 t2
interp _ _ _ = undefined -- Not defined on the surface language


-- | Interpreter for the intermediate language with lazy down casts
interpLD :: Exp -> IO (Either EvErr Value)
interpLD e = runErrorT $ runReaderT (interp applyCastLD applyLazy e) (Env {env = Map.empty})
