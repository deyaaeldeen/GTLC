{-# LANGUAGE TemplateHaskell, FlexibleContexts, NamedFieldPuns #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module Test where

import Control.Monad.Reader
import Test.QuickCheck
import Test.QuickCheck.Monadic
import qualified Distribution.TestSuite as TS

import GTLC.TypeChecker
import GTLC.Syntax
import GTLC.Eval

data Gamma = Gamma {ctx :: [(Name,Type)], size :: Int}

type TsMonad = ReaderT Gamma Gen

instance Arbitrary Operator where
  arbitrary = elements [Inc,Dec,ZeroQ]

instance Arbitrary Type where
  arbitrary = liftM2 Fun arbitrary arbitrary >>= \f -> elements [IntTy,BoolTy, f]


-- | Generates a variable name
genName :: Gen Name
genName = vectorOf 2 (elements ['a'..'z'])


-- | Wraps the result of elements in Maybe
elementsMaybe :: [a] -> Maybe (Gen a)
elementsMaybe [] = Nothing
elementsMaybe xs = Just (elements xs)


-- | Randomly selects a variable that has a specific type from the context
pickName :: MonadReader Gamma m => Type -> m (Maybe (Gen Exp))
pickName t1 = asks ctx >>= \c -> return (elementsMaybe [Var x | (x,t2) <- c, t2 == t1])


-- | Changes the size field of a gamma
newSize :: Int -> Gamma -> Gamma
newSize n g = g{size = n}


-- | Changes the size field of a gamma in reader monad
updtMSize :: (MonadReader Gamma m) => Int -> m a -> m a
updtMSize = local . newSize


-- | Extend the context with a new binding.
extendCtx :: (Name, Type) -> Gamma -> Gamma
extendCtx v g@(Gamma {ctx = cs}) = g{ctx = v:cs}


-- | Generates expressions for int expressions
genExpInt :: Gen Exp -> TsMonad Exp
genExpInt e = asks size >>= \s ->
  if s > 0
  then
    (updtMSize (s-1)) $ genExpInt $ liftM3 Op (elements [Inc,Dec]) e (return "")
  else
    lift e


-- | Generates an expression that has a ZeroQ on the top so the type of the result expression is BoolTy
genExpBool :: Gen Exp -> Gen Exp
genExpBool e = liftM3 Op (return ZeroQ) e (return "")


-- | Generates arbitrary type
genType :: Gen Type
genType = arbitrary


-- | Returns a list of consistent types for some type
consistent :: Type -> [Type]
consistent (Fun t1 t2) = (zipWith Fun (consistent t1) (consistent t2))
consistent t = [t]


-- | Generates a random consistent type for a specific type
genConsistentType :: Type -> Gen Type
genConsistentType = elements . consistent


-- | Generates application expressions
genExpApp :: Gen Type -> TsMonad Exp
genExpApp t = ask >>= \g@(Gamma{size = s}) ->
  if s > 0
  then
    lift t >>= \t2 -> lift $ genType >>= \t1 -> elements [t1,Dyn] >>= \td -> liftM3 App (runReaderT (genExp $ return (Fun td t2)) (newSize (s `div` 2) g)) (runReaderT (genExp $ genConsistentType t1) (newSize (s `div` 2) g)) (return "")
  else
    genExp t


-- | Generates an expression that has a specific type
genExp :: Gen Type -> TsMonad Exp
genExp t = lift t >>= \tp -> ask >>= \g@(Gamma{size = s}) -> pickName tp >>= \randVar ->
  case tp of
   IntTy -> let values = (1,liftM N arbitrary):(maybe [] (\x->[(2,x)]) randVar) in
             if s > 0
             then
               lift $ frequency (values ++ [(3,runReaderT (genExpIf tp) g),(4,runReaderT (genExpInt $ liftM N arbitrary) g),(4,runReaderT (genExpApp t) (newSize (s `div` 2) g))])
             else
               lift $ frequency values
   BoolTy -> let values = (1,liftM B arbitrary):(maybe [] (\x->[(2,x)]) randVar) in
              if s > 0
              then
                lift $ frequency (values ++ [(3,runReaderT (genExpIf tp) g),(4,genExpBool (runReaderT (genExpInt $ liftM N arbitrary) (newSize (s-1) g))),(4,runReaderT (genExpApp t) g)])
              else
                lift $ frequency values
   (Fun t1 t2) -> let values = (1,runReaderT (genExpAnnLam t1 t2) g):(1,runReaderT (genExpLam t1 t2) g):(maybe [] (\x-> [(2,x)]) randVar) in
                   if s > 0
                   then
                     lift $ frequency (values ++ [(3,runReaderT (genExpIf tp) g),(4,runReaderT (genExpApp t) g)])
                   else
                     lift $ frequency values
   Dyn -> undefined


-- | Generates conditional expressions
genExpIf :: Type -> TsMonad Exp
genExpIf t = ask >>= \g@(Gamma{size = s}) -> liftM4 If (updtMSize (s `div` 3) (genExp $ genConsistentType BoolTy)) (updtMSize (s `div` 3) (genExp $ genConsistentType t)) (updtMSize (s `div` 3) (genExp $ genConsistentType t)) (return "")


-- | Generates a lambda abstraction without annotation
genExpLam :: Type -> Type -> TsMonad Exp
genExpLam t1 t2 = ask >>= \g@(Gamma{size = s}) -> lift $ genName >>= \x -> liftM2 Lam (return x) (runReaderT (genExp $ return t2) (extendCtx (x,t1) (newSize (s-1) g)))


-- | Generates a lambda abstraction with annotation
genExpAnnLam :: Type -> Type -> TsMonad Exp
genExpAnnLam t1 t2 = ask >>= \g@(Gamma{size = s}) -> lift $ genName >>= \x -> liftM2 AnnLam (return (x,t1)) (runReaderT (genExp $ return t2) (extendCtx (x,t1) (newSize (s-1) g)))

instance Arbitrary Exp where
      arbitrary = sized $ \n -> runReaderT (genExp arbitrary) Gamma {ctx=[],size=n}

propTypePres :: Exp -> Property
propTypePres e = monadicIO $ do et1 <- run $ runTypeCheck e
                                _ <- case et1 of
                                      Right (ie,t1) ->
                                        do ve <- run $ interpLD ie
                                           case ve of
                                            Right v -> do et2 <- run $ runTypeCheck (valToExp v)
                                                          _ <- case et2 of
                                                                Right (_,t2) -> assert $ isConsistent t1 t2
                                                                Left _ -> fail "does not type check 1"
                                                          return ()
                                            Left _ -> fail "does not evaluate"
                                      Left _ -> fail "does not type check 2"
                                return ()


-- | Converts from QuickCheck result to Distribution.TestSuite result
-- https://www.fpcomplete.com/user/griba/quickCheck-in-test-suite-type-detailed
toTSResult :: Result -> TS.Result
toTSResult Success {} = TS.Pass
toTSResult GaveUp {} = TS.Fail "GaveUp"
toTSResult Failure {reason} = TS.Fail reason


-- | Run a quick check property for 1000 problem instances each with small size
runQuickCheck :: Testable p => p -> IO TS.Progress
runQuickCheck prop = quickCheckWithResult stdArgs {maxSuccess = 1000, maxSize = 3, chatty = True} prop >>= return . TS.Finished . toTSResult


-- | Run a bunch of tests
tests :: IO [TS.Test]
tests = return [TS.Test $ TS.TestInstance (runQuickCheck propTypePres) "Type Preservation" ["tag"] [] undefined]


main :: IO [TS.Test]
main =  tests
