{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fwarn-incomplete-patterns #-}

module GTLC.Eval(interpD, interpUD) where

import Control.Monad.Error (runErrorT, throwError)
import Control.Monad.Reader (runReaderT, asks, ask)
import Control.Monad.State (runStateT, get, put)
import Data.HashMap.Lazy as H
import qualified Data.Map as M

import GTLC.Syntax
import GTLC.TypeChecker


-- | Applies a coercion to an expression.
mkCoerce :: Value -> Coercion -> EvMonad Value
mkCoerce _ (FailC _ _) = throwError EvCoercionFailed
mkCoerce _ (FunC (FailC _ _) _) = throwError EvCoercionFailed
mkCoerce _ (FunC _ (FailC _ _)) = throwError EvCoercionFailed
mkCoerce _ (RefC (FailC _ _) _) = throwError EvCoercionFailed
mkCoerce _ (RefC _ (FailC _ _)) = throwError EvCoercionFailed
mkCoerce v (IdC _) = return v
mkCoerce (VC v c1) c2 = mkCoerce v $ (seqL mkCoerceLUD) c1 c2
mkCoerce v c = return $ VC v c


-- | Performs coerced application.
apply :: Value -> Value -> EvMonad Value
apply (Closure (x,_) e env) v2 = extendEvEnv (x,v2) env $ interp e
apply (VC v (FunC c d)) v2 = mkCoerce v2 c >>= apply v >>= \v' -> mkCoerce v' d
apply _ _ = throwError EvCallNonFunctionNonCast


-- | Performs coerced de-reference.
deref :: Value -> EvMonad Value
deref (VAddr a) = get >>= \x@(EvHeap {evHeap = h}) -> maybe (throwError EvBadLocation) return (H.lookup a h)
deref (VC v (RefC _ d)) = deref v >>= \v' -> mkCoerce v' d
deref _ = throwError EvBadReference


-- | Performs coerced assignment.
assign :: Value -> Value -> EvMonad Value
assign (VAddr a) v2 = get >>= \x@(EvHeap {evHeap = h}) ->
                               case H.lookup a h of
                                Nothing -> throwError EvBadLocation
                                _ -> get >>= \x'@(EvHeap {evHeap = h'}) -> let h'' = H.adjust (const v2) a h' in put (x'{evHeap = h''}) >> return v2
assign (VC v1 (RefC c d)) v2 = mkCoerce v2 c >>= assign v1 >>= \e -> mkCoerce e d
assign _ _ = throwError EvBadReference


-- | Interprets the intermediate language.
interp :: IExp -> EvMonad Value
interp (IC e c) = interp e >>= \v -> mkCoerce v c
interp (IN x) = return (VN x)
interp (IB x) = return (VB x)
interp (IOp Inc e) = interp e >>= \(VN v) -> return $ VN(v+1)
interp (IOp Dec e) = interp e >>= \(VN v) -> return $ VN(v-1)
interp (IOp ZeroQ e) = interp e >>= \(VN v) -> return $ VB(v == 0)
interp (IIf e1 e2 e3) = interp e1 >>= \(VB v) -> if v then interp e2 else interp e3
interp (IVar v) = asks evEnv >>= \env -> maybe (throwError (EvUndefinedVar v)) return (M.lookup v env)
interp (IApp e1 e2) = interp e1 >>= \v1 -> interp e2 >>= apply v1
interp (IAnnLam x e) = ask >>= return . (Closure x e)
interp (IGRef e) = interp e >>= \v -> get >>= \x@(EvHeap {evHeap = h, evTop = a}) -> put (x {evHeap = H.insert a v h, evTop = a+1}) >>= \_ -> return $ VAddr a
interp (IGDeRef e) = interp e >>= deref
interp (IGAssign e1 e2) = interp e1 >>= \v1 -> interp e2 >>= assign v1
interp (ILet var e1 e2) = interp e1 >>= \v1 -> ask >>= \env -> extendEvEnv (var, v1) env $ interp e2


-- | Interpreter for the intermediate language with lazy down casts.
interpD :: IExp -> IO (Either EvErr (Value,EvHeap))
interpD e = runErrorT $ runReaderT (runStateT (interp e) (EvHeap {evHeap=H.empty, evTop = 0})) (EvEnv {evEnv = M.empty}) >>= return


-- | Interpreter for the intermediate language with lazy up down casts.
interpUD :: IExp -> IO (Either EvErr (Value,EvHeap))
interpUD e = runErrorT $ runReaderT (runStateT (interp e) (EvHeap {evHeap=H.empty, evTop = 0})) (EvEnv {evEnv = M.empty}) >>= return
