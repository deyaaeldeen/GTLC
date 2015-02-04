{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

module Testing(test,test5) where

import Control.Applicative
import Control.Monad.Reader
import Data.Maybe
import Test.QuickCheck
import Test.QuickCheck.Monadic

import TypeChecker
import Syntax

data Gamma = Gamma {ctx :: [(Name,Type)], size :: Int}

type TsMonad = ReaderT Gamma Gen

instance Arbitrary Operator where
  arbitrary = elements [Inc,Dec,ZeroQ]

instance Arbitrary Type where
  arbitrary = liftM2 Fun arbitrary arbitrary >>= \f -> elements [IntTy,BoolTy,Dyn, f]


-- | generate a variable name
genName :: Gen Name
genName = vectorOf 2 (elements ['a'..'z'])


-- | Wraps the result of elements in Maybe
elementsMaybe :: [a] -> Maybe (Gen a)
elementsMaybe [] = Nothing
elementsMaybe xs = Just (elements xs)


-- | Randomly selects a variable that has a specific type from the context
pickName :: MonadReader Gamma m => Type -> m (Maybe (Gen Exp))
pickName t1 = asks ctx >>= \ctx -> return (elementsMaybe [Var x | (x,t2) <- ctx, t2 == t1])


-- | Changes the size field of a gamma
mSize :: (MonadReader Gamma m) => Int -> m a -> m a
mSize s = local (\ m -> m { size = s })


-- | Extend the context with a new binding.
extendCtx :: (MonadReader Gamma m) => (Name, Type) -> m a -> m a
extendCtx v = local (\ m@(Gamma {ctx = cs}) -> m { ctx = v:cs })


-- | Generates expressions for int expressions
genExpInt :: Gen Exp -> TsMonad Exp
genExpInt e = asks size >>= \size ->
  if size > 0
  then
    (mSize (size-1)) $ genExpInt $ liftM3 Op (elements [Inc,Dec]) e (return "")
  else
    lift e


-- | Generates an expression that has a ZeroQ on the top so the type of the result expression is BoolTy
genExpBool :: Gen Exp -> Gen Exp
genExpBool e = liftM3 Op (return ZeroQ) e (return "")


-- | Generates arbitrary types
genType :: Gen Type
genType = arbitrary


-- | Generates application expressions
genExpApp :: Gen Type -> TsMonad Exp
genExpApp t = ask >>= \gamma -> let s = size gamma in
  if s > 0
  then
    lift t >>= \t2 -> lift $ genType >>= \t1 -> liftM3 App (runReaderT (genExp $ return (Fun t1 t2)) gamma) (runReaderT (genExp $ return t1) gamma) (return "")
  else
    genExp t


-- | Generates an expression that has a specific type
genExp :: Gen Type -> TsMonad Exp
genExp t = lift t >>= \tp -> ask >>= \gamma -> pickName tp >>= \randVar ->
  let s = size gamma in
   case tp of
    IntTy -> let nats = (1,liftM N arbitrary)
                 values = maybe [nats] (\x->[(2,x), nats]) randVar in
              if s > 0
              then
                lift $ frequency (values ++ [(3,runReaderT (genExpIf tp) gamma),(4,runReaderT (genExpInt $ liftM N arbitrary) gamma),(4,runReaderT (mSize (s `div` 2) (genExpApp t)) gamma)])
              else
                lift $ frequency values
    BoolTy -> let bools = (1,liftM B arbitrary)
                  values = maybe [bools] (\x->[(2,x), bools]) randVar in
               if s > 0
               then
                 lift $ frequency (values ++ [(3,runReaderT (genExpIf tp) gamma),(4,genExpBool (runReaderT (genExpInt $ liftM N arbitrary) gamma)),(4,runReaderT (mSize (s `div` 2) (genExpApp t)) gamma)])
               else
                 lift $ frequency values
    (Fun t1 t2) -> let funs = [(1,runReaderT (mSize (s-1) (genExpLam t1 t2)) gamma),(1,runReaderT (mSize (s-1) (genExpAnnLam t1 t2)) gamma)]
                       values = maybe funs (\x-> (2,x):funs) randVar in
                    if s > 0
                    then
                      lift $ frequency (values ++ [(3,runReaderT (genExpIf tp) gamma),(4,runReaderT (mSize (s `div` 2) (genExpApp t)) gamma)])
                    else
                      lift $ frequency values
    Dyn -> let values = maybe [] (\x->[(2,x)]) randVar in
            lift (liftM N arbitrary)


-- | Generates if expressions
genExpIf :: Type -> TsMonad Exp
genExpIf t = ask >>= \gamma -> liftM4 If (mSize ((size gamma) `div` 3) (genExp $ return BoolTy)) (mSize ((size gamma) `div` 3) (genExp $ return t)) (mSize ((size gamma)-1) (genExp $ return t)) (return "")


-- | Generates a lambda abstraction without annotation
genExpLam :: Type -> Type -> TsMonad Exp
genExpLam t1 t2 = ask >>= \gamma -> lift $ genName >>= \x -> liftM2 Lam (return x) (runReaderT (mSize ((size gamma)-1) (extendCtx (x,t1) (genExp $ return t2))) gamma)


-- | Generates a lambda abstraction with annotation
genExpAnnLam :: Type -> Type -> TsMonad Exp
genExpAnnLam t1 t2 = ask >>= \gamma -> lift $ genName >>= \x -> liftM2 AnnLam (return (x,t1)) (runReaderT (mSize ((size gamma)-1) (extendCtx (x,t1) (genExp $ return t2))) gamma)

instance Arbitrary Exp where
      arbitrary = sized $ \n -> runReaderT (genExp arbitrary) Gamma {ctx=[],size=n}

prop_id :: Exp -> Property
prop_id e = monadicIO $ do t <- run $ runTypeCheck e
                           _ <- case t of
                             Right x -> assert $ x == x
                             Left z -> fail "does not type check"
                           return ()


return []
test = $verboseCheckAll
test5 =  verboseCheckWith Args {replay=Nothing,maxSuccess=10000,maxSize=5,chatty=True,maxDiscardRatio=10} prop_id
