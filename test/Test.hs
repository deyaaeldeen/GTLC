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
genName = vectorOf 2 $ elements ['a'..'z']


-- | Wraps the result of elements in Maybe
elementsMaybe :: [a] -> Maybe (Gen a)
elementsMaybe [] = Nothing
elementsMaybe xs = Just $ elements xs


-- | Randomly selects a variable that has a specific type from the context
pickName :: MonadReader Gamma m => Type -> m (Maybe (Gen SExp))
pickName t1 = asks ctx >>= \c -> return $ elementsMaybe [Var x | (x,t2) <- c, t2 == t1]


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
genSExpInt :: Gen SExp -> TsMonad SExp
genSExpInt e = asks size >>= \s ->
  if s > 0
  then
    updtMSize (s-1) $ genSExpInt $ liftM2 Op (elements [Inc,Dec]) e
  else
    lift e


-- | Generates an expression that has a ZeroQ on the top so the type of the result expression is BoolTy
genSExpBool :: Gen SExp -> Gen SExp
genSExpBool e = liftM2 Op (return ZeroQ) e


-- | Generates arbitrary type
genType :: Gen Type
genType = arbitrary


-- | Returns a list of consistent types for some type
consistent :: Type -> [Type]
consistent (Fun t1 t2) = zipWith Fun (consistent t1) (consistent t2)
consistent t = [t]


-- | Generates a random consistent type for a specific type
genConsistentType :: Type -> Gen Type
genConsistentType = elements . consistent


-- | Generates application expressions
genSExpApp :: Gen Type -> TsMonad SExp
genSExpApp t = ask >>= \g@(Gamma{size = s}) ->
  if s > 0
  then
    lift t >>= \t2 -> lift $ genType >>= \t1 -> elements [t1,Dyn] >>= \td -> liftM2 App (runReaderT (genSExp $ return $ Fun td t2) (newSize (s `div` 2) g)) (runReaderT (genSExp $ genConsistentType t1) (newSize (s `div` 2) g))
  else
    genSExp t


-- | Generates an expression that has a specific type
genSExp :: Gen Type -> TsMonad SExp
genSExp t = lift t >>= \tp -> ask >>= \g@(Gamma{size = s}) -> pickName tp >>= \randVar ->
  case tp of
   IntTy -> let values = (1,liftM N arbitrary):(maybe [] (\x->[(2,x)]) randVar) in
             if s > 0
             then
               lift $ frequency (values ++ [(3,runReaderT (genSExpIf tp) g),(4,runReaderT (genSExpInt $ liftM N arbitrary) g),(4,runReaderT (genSExpApp t) (newSize (s `div` 2) g))])
             else
               lift $ frequency values
   BoolTy -> let values = (1,liftM B arbitrary):(maybe [] (\x->[(2,x)]) randVar) in
              if s > 0
              then
                lift $ frequency (values ++ [(3,runReaderT (genSExpIf tp) g),(4,genSExpBool $ runReaderT (genSExpInt $ liftM N arbitrary) (newSize (s-1) g)),(4,runReaderT (genSExpApp t) g)])
              else
                lift $ frequency values
   (Fun t1 t2) -> let values = (1,runReaderT (genSExpAnnLam t1 t2) g):(1,runReaderT (genSExpLam t1 t2) g):(maybe [] (\x-> [(2,x)]) randVar) in
                   if s > 0
                   then
                     lift $ frequency (values ++ [(3,runReaderT (genSExpIf tp) g),(4,runReaderT (genSExpApp t) g)])
                   else
                     lift $ frequency values
   Dyn -> undefined


-- | Generates conditional expressions
genSExpIf :: Type -> TsMonad SExp
genSExpIf t = ask >>= \g@(Gamma{size = s}) -> liftM3 If (updtMSize (s `div` 3) (genSExp $ genConsistentType BoolTy)) (updtMSize (s `div` 3) (genSExp $ genConsistentType t)) (updtMSize (s `div` 3) (genSExp $ genConsistentType t))


-- | Generates a lambda abstraction without annotation
genSExpLam :: Type -> Type -> TsMonad SExp
genSExpLam t1 t2 = ask >>= \g@(Gamma{size = s}) -> lift $ genName >>= \x -> liftM2 Lam (return x) (runReaderT (genSExp $ return t2) (extendCtx (x,t1) (newSize (s-1) g)))


-- | Generates a lambda abstraction with annotation
genSExpAnnLam :: Type -> Type -> TsMonad SExp
genSExpAnnLam t1 t2 = ask >>= \g@(Gamma{size = s}) -> lift $ genName >>= \x -> liftM2 AnnLam (return (x,t1)) (runReaderT (genSExp $ return t2) (extendCtx (x,t1) (newSize (s-1) g)))

instance Arbitrary SExp where
      arbitrary = sized $ \n -> runReaderT (genSExp arbitrary) Gamma {ctx=[],size=n}

propTypePresLD :: SExp -> Property
propTypePresLD e = monadicIO $ do et1 <- run $ runTypeCheck e
                                  _ <- case et1 of
                                        Right (ie,t1) ->
                                          do ve <- run $ interpLD ie
                                             case ve of
                                              Right v -> do et2 <- run $ runTypeCheck (valToSExp v)
                                                            _ <- case et2 of
                                                                  Right (_,t2) -> assert $ isConsistent t1 t2
                                                                  Left _ -> fail "does not type check 1"
                                                            return ()
                                              Left _ -> fail "does not evaluate"
                                        Left _ -> fail "does not type check 2"
                                  return ()


propTypePresLUD :: SExp -> Property
propTypePresLUD e = monadicIO $ do et1 <- run $ runTypeCheck e
                                   _ <- case et1 of
                                         Right (ie,t1) ->
                                           do ve <- run $ interpLUD ie
                                              case ve of
                                               Right v -> do et2 <- run $ runTypeCheck (valToSExp v)
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
runQuickCheck prop = quickCheckWithResult stdArgs {maxSuccess = 700, maxSize = 3, chatty = True} prop >>= return . TS.Finished . toTSResult


-- | Run a bunch of tests
tests :: IO [TS.Test]
tests = return [TS.Test $ TS.TestInstance (runQuickCheck propTypePresLD) "Type Preservation LD" ["tag"] [] undefined,
                TS.Test $ TS.TestInstance (runQuickCheck propTypePresLUD) "Type Preservation LUD" ["tag"] [] undefined]


main :: IO [TS.Test]
main =  tests
