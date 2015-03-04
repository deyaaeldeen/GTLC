{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fwarn-incomplete-patterns #-}

module GTLC.Eval(interpD, interpUD) where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.HashMap.Lazy as H
import qualified Data.Map as M

import GTLC.Syntax
import GTLC.TypeChecker


-- | Interprets the intermediate language.
interp :: IExp -> EvMonad Value
-- error detection
interp (IC _ (FailC _ _)) = throwError EvCoercionFailed
interp (IC e (FunC f@(FailC _ _) _)) = interp $ IC e f
interp (IC e (FunC _ f@(FailC _ _))) = interp $ IC e f
interp (IC e (RefC f@(FailC _ _) _)) = interp $ IC e f
interp (IC e (RefC _ f@(FailC _ _))) = interp $ IC e f
-- applying coercions
interp (IApp (IC e1 (FunC c d)) e2) = interp $ IC (IApp e1 $ IC e2 c) d
interp (IGDeRef (IC e (RefC _ d))) = interp $ IC (IGDeRef e) d
interp (IGAssign (IC e1 (RefC c d)) e2) = interp $ IC (IGAssign e1 $ IC e2 c) d
interp (IC e (IdC _)) = interp e
interp (IC (IC e d) c) = interp $ IC e (seqL mkCoerceLUD d c)
-- standard evaluation rules
interp (IC e _) = interp e
interp (IN x) = return (VN x)
interp (IB x) = return (VB x)
interp (IOp Inc e) = interp e >>= \(VN v) -> return $ VN(v+1)
interp (IOp Dec e) = interp e >>= \(VN v) -> return $ VN(v-1)
interp (IOp ZeroQ e) = interp e >>= \(VN v) -> return $ VB(v == 0)
interp (IIf e1 e2 e3) = interp e1 >>= \(VB v) -> if v then interp e2 else interp e3
interp (IVar v) = asks evEnv >>= \env -> maybe (throwError (EvUndefinedVar v)) return (M.lookup v env)
interp (IApp e1 e2) = interp e1 >>= \case
  (Closure (x,_) e env) -> interp e2 >>= \v -> extendEvEnv (x,v) env $ interp e
  _ -> throwError EvCallNonFunctionNonCast
interp (IAnnLam x e) = ask >>= return . (Closure x e)
interp (IGRef e) = interp e >>= \v -> get >>= \x@(EvHeap {evHeap = h, evTop = a}) -> put (x {evHeap = H.insert a v h, evTop = a+1}) >>= \_ -> return $ VAddr a
interp (IGDeRef e) = interp e >>= \case
  (VAddr a) -> get >>= \x@(EvHeap {evHeap = h}) -> maybe (throwError EvBadLocation) return (H.lookup a h)
  _ -> throwError EvBadReference
interp (IGAssign e1 e2) = interp e1 >>= \case
  (VAddr a) -> get >>= \x@(EvHeap {evHeap = h}) ->
                        case H.lookup a h of
                         Nothing -> throwError EvBadLocation
                         _ -> interp e2 >>= \v2 -> get >>= \x'@(EvHeap {evHeap = h'}) -> let h'' = H.adjust (const v2) a h' in put (x'{evHeap = h''}) >> return v2
  _ -> throwError EvBadReference
interp (ILet var e1 e2) = interp e1 >>= \v1 -> ask >>= \env -> extendEvEnv (var, v1) env $ interp e2


-- | Interpreter for the intermediate language with lazy down casts.
interpD :: IExp -> IO (Either EvErr (Value,EvHeap))
interpD e = runErrorT $ runReaderT (runStateT (interp e) (EvHeap {evHeap=H.empty, evTop = 0})) (EvEnv {evEnv = M.empty}) >>= return


-- | Interpreter for the intermediate language with lazy up down casts.
interpUD :: IExp -> IO (Either EvErr (Value,EvHeap))
interpUD e = runErrorT $ runReaderT (runStateT (interp e) (EvHeap {evHeap=H.empty, evTop = 0})) (EvEnv {evEnv = M.empty}) >>= return
