{-# LANGUAGE FlexibleContexts, NamedFieldPuns, LambdaCase #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fwarn-incomplete-patterns #-}

module Test (main,tests,test) where

import Control.Monad.Reader (MonadReader, runReaderT, lift, liftM, liftM2, liftM3, asks, ask)
import Test.QuickCheck (Arbitrary, Gen, Property, Args (..), Result (..), Testable, stdArgs, verboseCheckWithResult, verboseCheckWith, vectorOf, elements, arbitrary, frequency, sized)
import Test.QuickCheck.Monadic (monadicIO, run, assert)
import qualified Data.Map.Lazy as M
import qualified Distribution.TestSuite as TS

import GTLC.TypeChecker
import GTLC.Syntax
import GTLC.Eval


-- | Runs a TsMonad and extracts the final value from it.
runTsMonad :: TsGamma -> TsMonad SExp -> Gen SExp
runTsMonad env e = runReaderT e env


-- | Generates a variable name.
genName :: Gen Name
genName = vectorOf 2 $ elements ['a'..'z']


-- | Wraps the result of elements in Maybe.
elementsMaybe :: [a] -> Maybe (Gen a)
elementsMaybe [] = Nothing
elementsMaybe xs = Just $ elements xs


-- | Randomly selects a variable that has a specific type from the context and apply a function to it.
pickName :: MonadReader TsGamma m => Type -> (Name -> a) -> m (Maybe (Gen a))
pickName t1 f = asks tsCtx >>= \c -> return $ elementsMaybe $ map (f . fst) $ M.toList $ M.filter ((==) t1) c


-- | Generates expressions for int expressions.
genSExpInt :: Gen SExp -> TsMonad SExp
genSExpInt e = asks tsSize >>= \s -> if s > 0 then updtMSize (s-1) $ genSExpInt $ liftM2 Op (elements [Inc,Dec]) e else lift e


-- | Generates an expression that has a ZeroQ on the top so the type of the result expression is BoolTy.
genSExpBool :: Gen SExp -> Gen SExp
genSExpBool = liftM2 Op $ return ZeroQ


-- | Generates arbitrary type.
genType :: Gen Type
genType = arbitrary


-- | Returns a list of consistent types for some type.
consistent :: Type -> [Type]
consistent (Fun t1 t2) = zipWith Fun (consistent t1) $ consistent t2
consistent (GRefTy t) = map GRefTy $ consistent t
consistent t = [t]


-- | Generates a random consistent type for a specific type.
genConsistentType :: Type -> Gen Type
genConsistentType = elements . consistent


-- | Generates application expressions.
genSExpApp :: Type -> TsMonad SExp
genSExpApp t = asks tsSize >>= \s -> lift genType >>= \t1' -> liftM2 App (updtMSize (s `div` 2) (genSExp $ return $ Fun t1' t)) (updtMSize (s `div` 2) (genSExp $ genConsistentType t1'))


-- | Generates an expression that has a specific type.
genSExp :: Gen Type -> TsMonad SExp
genSExp t = ask >>= \g@(TsGamma{tsSize = s}) -> lift t >>= \t' -> pickName t' Var >>= \randVar -> pickName (GRefTy t') (GDeRef . Var) >>= \randRef -> pickName (GRefTy t') Var >>= \randRefAs ->
  let values = ((1, genDefaultVal t'):(maybe [] (\x->[(2,x)]) randVar)) ++ maybe [] (\x->[(2,x)]) randRef in
  lift $ frequency $ if s <= 0 then values else (++) (((3,runTsMonad g $ genSExpIf t'):(3,runTsMonad g $ genSExpApp t'):(3,runTsMonad g $ genSExpLetRef t'):values) ++ maybe [] (\x->[(3,runTsMonad g $ genSExpAssign t' x)]) randRefAs) $
  case t' of
   IntTy -> [(4,runTsMonad g $ genSExpInt $ liftM N arbitrary)]
   BoolTy -> [(4,genSExpBool $ runTsMonad (newSize (s-1) g) $ genSExpInt $ liftM N arbitrary)]
   (Fun t1 t2) -> [(4,runTsMonad g $ genSExpFun t1 t2)]
   (GRefTy t'') -> [(4,runTsMonad g $ genSExpRef t'')]
   Dyn -> [(1,runTsMonad g $ genSExp arbitrary)]


-- | Generates assignment expressions.
genSExpAssign :: Type -> Gen SExp -> TsMonad SExp
genSExpAssign t x = asks tsSize >>= \s -> liftM2 GAssign (lift x) $ updtMSize (s-1) $ genSExp $ genConsistentType t


-- Generates a let expression with a reference.
genSExpLetRef :: Type -> TsMonad SExp
genSExpLetRef t = asks tsSize >>= \s -> (lift $ genName) >>= \x -> (lift $ genType) >>= \t' -> liftM3 Let (return x) (updtMSize (s `div` 2) $ genSExp $ return $ GRefTy t') $ updtMSize (s `div` 2) $ extendTsCtx (x, GRefTy t') $ genSExp $ return t


-- | Generates a reference expression.
genSExpRef :: Type -> TsMonad SExp
genSExpRef t = asks tsSize >>= \s -> liftM GRef $ updtMSize (s-1) $ genSExp $ return t


-- | Generates conditional expressions.
genSExpIf :: Type -> TsMonad SExp
genSExpIf t = asks tsSize >>= \s -> liftM3 If (updtMSize (s `div` 3) $ genSExp $ genConsistentType BoolTy) (updtMSize (s `div` 3) $ genSExp $ genConsistentType t) $ updtMSize (s `div` 3) $ genSExp $ genConsistentType t


-- | Generates a lambda abstraction without annotation.
genSExpLam :: Type -> TsMonad SExp
genSExpLam t = asks tsSize >>= \s -> (lift $ genName) >>= \x -> liftM2 Lam (return x) $ updtMSize (s-1) $ extendTsCtx (x,Dyn) $ genSExp $ return t


-- | Generates a lambda abstraction with annotation.
genSExpAnnLam :: Type -> Type -> TsMonad SExp
genSExpAnnLam t1 t2 = asks tsSize >>= \s -> (lift $ genName) >>= \x -> liftM2 AnnLam (return (x,t1)) $ updtMSize (s-1) $ extendTsCtx (x,t1) $ genSExp $ return t2


-- | Generates a default value for a type.
genDefaultVal :: Type -> Gen SExp
genDefaultVal IntTy = liftM N arbitrary
genDefaultVal BoolTy = liftM B arbitrary
genDefaultVal (Fun Dyn t) = genName >>= \x -> genDefaultVal t >>= \e -> (if t == Dyn then elements [Var x, e] else elements [e]) >>= \e' -> elements[B True, B False] >>= \(B b) -> if b then liftM2 Lam (return x) (return e) else liftM2 AnnLam (return (x,Dyn)) (return e')
genDefaultVal (Fun t1 t2) = genName >>= \x -> genDefaultVal t2 >>= \e -> (if t1 == t2 then elements [Var x, e] else elements [e]) >>= \e' -> liftM2 Lam (return x) (return e')
genDefaultVal (GRefTy t) = liftM GRef $ genDefaultVal t
genDefaultVal Dyn = return $ Lam "x" (Var "x")


-- | Generates a lambda abstraction.
genSExpFun :: Type -> Type -> TsMonad SExp
genSExpFun Dyn t2 = (lift $ elements[B True, B False]) >>= \(B b) -> if b then genSExpLam t2 else genSExpAnnLam Dyn t2
genSExpFun t1 t2 = genSExpAnnLam t1 t2


instance Arbitrary SExp where
      arbitrary = sized $ \n -> runTsMonad (TsGamma {tsCtx=M.empty,tsSize=n}) $ genSExp arbitrary


-- | Tests type preservation.
propTypePres :: (SExp -> IO (Either TyErr (IExp, Type))) -> (IExp -> IO (Either EvErr (Value,EvHeap))) -> SExp -> Property
propTypePres typecheck interp e = monadicIO $ run (typecheck e) >>= \case
  Right (ie,t1) -> run (interp ie) >>= \case
    Right v -> run (typecheck $ valToSExp v) >>= \case
      Right (_,t2) -> assert $ isConsistent t1 t2
      Left _ -> fail "does not type check 1"
    Left _ -> fail "does not evaluate"
  Left _ -> fail "does not type check 2"


-- | Stress tests the system with a large number of generated instances each is of a big size.
test :: IO ()
test = verboseCheckWith Args {replay=Nothing,maxSuccess=10000,maxSize=100,chatty=True,maxDiscardRatio=10} (propTypePres runTypeCheck interpUD)


-- | Converts from QuickCheck result to Distribution.TestSuite result.
-- https://www.fpcomplete.com/user/griba/quickCheck-in-test-suite-type-detailed
toTSResult :: Result -> TS.Result
toTSResult Success {} = TS.Pass
toTSResult GaveUp {} = TS.Fail "GaveUp"
toTSResult Failure {reason} = TS.Fail reason


-- | Run a quick check property.
runQuickCheck :: Testable p => p -> IO TS.Progress
runQuickCheck prop = verboseCheckWithResult stdArgs {maxSuccess = 255, maxSize = 5, chatty = True, maxDiscardRatio=10} prop >>= return . TS.Finished . toTSResult


-- | Run a bunch of tests.
tests :: IO [TS.Test]
tests = return [TS.Test $ TS.TestInstance (runQuickCheck $ propTypePres runTypeCheck interpD) "Type Preservation D" ["D"] [] undefined,
                TS.Test $ TS.TestInstance (runQuickCheck $ propTypePres runTypeCheck interpUD) "Type Preservation UD" ["UD"] [] undefined]


main :: IO [TS.Test]
main =  tests
