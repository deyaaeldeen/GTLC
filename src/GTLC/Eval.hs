{-# LANGUAGE NamedFieldPuns, FlexibleContexts, ViewPatterns #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fwarn-incomplete-patterns #-}

module GTLC.Eval(interpLD, interpLUD) where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.HashMap.Lazy as H
import qualified Data.Map as M

import GTLC.Syntax
import GTLC.TypeChecker


-- | Extend the environment with a new binding.
extendEnv :: (MonadReader Env m) => (Name, Value) -> Env -> m a -> m a
extendEnv (x,v) m@(Env {env = en}) = local (\_ -> m { env = M.insert x v en })


type AppT = Value -> Value -> EvMonad Value


-- | Performs function application.
applyLazy :: AppT
applyLazy (Closure (x,_) e env) v = extendEnv (x,v) env $ interp applyLazy e
applyLazy _ _ = throwError EvCallNonFunctionNonCast


-- | Interprets the intermediate language.
interp :: AppT -> IExp -> EvMonad Value
-- error detection
interp app (IC _ (FailC _ _)) = throwError EvCoercionFailed
interp app (IC e (FunC (FailC t1 t2) _)) = interp app $ IC e (FailC t1 t2)
interp app (IC e (FunC _ (FailC t1 t2))) = interp app $ IC e (FailC t1 t2)
interp app (IC e (RefC (FailC t1 t2) _)) = interp app $ IC e (FailC t1 t2)
interp app (IC e (RefC _ (FailC t1 t2))) = interp app $ IC e (FailC t1 t2)
-- combining coercions
interp app (IApp (IC e1 (FunC c d)) e2) = interp app $ IC (IApp e1 $ IC e2 c) d
interp app (IGDeRef (IC e (RefC _ d))) = interp app $ IC (IGDeRef e) d
interp app (IGAssign (IC e1 (RefC c d)) e2) = interp app $ IC (IGAssign e1 (IC e2 c)) d
interp app (IC e (IdC _)) = interp app e
interp app (IC (IC e d) c) = interp app $ IC e (seqL mkCoerceLUD d c)
-- standard evaluation rules
interp app (IC e _) = interp app e
interp _ (IN x) = return (VN x)
interp _ (IB x) = return (VB x)
interp app (IOp Inc e) = interp app e >>= \(VN v) -> return $ VN(v+1)
interp app (IOp Dec e) = interp app e >>= \(VN v) -> return $ VN(v-1)
interp app (IOp ZeroQ e) = interp app e >>= \(VN v) -> return $ VB(v == 0)
interp app (IIf e1 e2 e3) = interp app e1 >>= \(VB v) -> if v then interp app e2 else interp app e3
interp _ (IVar v) = asks env >>= \env -> maybe (throwError (EvUndefinedVar v)) return (M.lookup v env)
interp app (IApp e1 e2) = interp app e1 >>= \f -> interp app e2 >>= app f
interp app (IAnnLam x e) = ask >>= return . (Closure x e)
interp app (IGRef e) = interp app e >>= \v -> get >>= \x@(Heap {heap = h, top = a}) -> put (Heap {heap = H.insert a v h, top = a+1}) >>= \_ -> return $ VAddr a
interp app (IGDeRef e) = interp app e >>= \v -> case v of
                                                 (VAddr a) -> get >>= \x@(Heap {heap = h}) -> maybe (throwError EvBadLocation) return (H.lookup a h)
                                                 _ -> throwError EvBadReference
interp app (IGAssign e1 e2) = interp app e1 >>= \v -> case v of
                                                       (VAddr a) -> get >>= \x@(Heap {heap = h}) ->
                                                                             case H.lookup a h of
                                                                              Nothing -> throwError EvBadLocation
                                                                              _ -> interp app e2 >>= \v2 -> let h' = H.adjust (const v2) a h in put (x{heap = h'}) >> return v2
                                                       _ -> throwError EvBadReference


-- | Interpreter for the intermediate language with lazy down casts.
interpLD :: IExp -> IO (Either EvErr Value)
interpLD e = runErrorT $ runReaderT (runStateT (interp applyLazy e) (Heap {heap=H.empty, top = 0})) (Env {env = M.empty}) >>= return . fst


-- | Interpreter for the intermediate language with lazy up down casts.
interpLUD :: IExp -> IO (Either EvErr Value)
interpLUD e = runErrorT $ runReaderT (runStateT (interp applyLazy e) (Heap {heap=H.empty, top = 0})) (Env {env = M.empty}) >>= return . fst
