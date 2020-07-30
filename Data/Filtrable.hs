module Data.Filtrable
  ( Filtrable (..)
  , (<$?>), (<*?>)
  , nub, nubBy, nubOrd, nubOrdBy
  ) where

import Prelude hiding (filter)

import Control.Applicative
import Control.Monad
import qualified Control.Monad.Trans.State as M
import Data.Bool (bool)
import Data.Functor.Compose
import Data.Functor.Product
import Data.Functor.Sum
import Data.Proxy
import Data.Traversable

import qualified Data.Set.Private as Set

-- | Laws:
--
-- * @'mapMaybe' 'Just' = id@
--
-- * @'mapMaybe' f = 'catMaybes' ∘ 'fmap' f@
--
-- * @'catMaybes' = 'mapMaybe' id@
--
-- * @'filter' f = 'mapMaybe' (\\ x -> 'bool' 'Nothing' ('Just' x) (f x))@
--
-- * @'mapMaybe' g . 'mapMaybe' f = 'mapMaybe' (g '<=<' f)@
--
--   Laws if @'Foldable' f@:
--
-- * @'foldMap' g . 'filter' f = 'foldMap' (\\ x -> 'bool' 'mempty' (g x) (f x))@
class Functor f => Filtrable f where
    {-# MINIMAL mapMaybe | catMaybes #-}

    mapMaybe :: (a -> Maybe b) -> f a -> f b
    mapMaybe f = catMaybes . fmap f

    catMaybes :: f (Maybe a) -> f a
    catMaybes = mapMaybe id

    filter :: (a -> Bool) -> f a -> f a
    filter f = mapMaybe ((<$) <*> guard . f)

    mapMaybeA :: (Traversable f, Applicative p) => (a -> p (Maybe b)) -> f a -> p (f b)
    mapMaybeA f xs = catMaybes <$> traverse f xs

    filterA :: (Traversable f, Applicative p) => (a -> p Bool) -> f a -> p (f a)
    filterA f = mapMaybeA (\ x -> (x <$) . guard <$> f x)

    mapEither :: (a -> Either b c) -> f a -> (f b, f c)
    mapEither f = (,) <$> mapMaybe (either Just (pure Nothing) . f)
                      <*> mapMaybe (either (pure Nothing) Just . f)

    mapEitherA :: (Traversable f, Applicative p) => (a -> p (Either b c)) -> f a -> p (f b, f c)
    mapEitherA f = liftA2 (,) <$> mapMaybeA (fmap (Just `either` pure Nothing) . f)
                              <*> mapMaybeA (fmap (pure Nothing `either` Just) . f)

    partitionEithers :: f (Either a b) -> (f a, f b)
    partitionEithers = mapEither id

instance Filtrable [] where
    mapMaybe f = foldr (maybe id (:) . f) []

    mapMaybeA _ [] = pure []
    mapMaybeA f (x:xs) = maybe id (:) <$> f x <*> mapMaybeA f xs

instance Filtrable Maybe where
    mapMaybe = (=<<)
    catMaybes = join

instance Filtrable Proxy where
    mapMaybe _ Proxy = Proxy

instance Filtrable (Const a) where
    mapMaybe _ (Const x) = Const x

instance (Filtrable f, Filtrable g) => Filtrable (Product f g) where
    mapMaybe f (Pair as bs) = Pair (mapMaybe f as) (mapMaybe f bs)

instance (Filtrable f, Filtrable g) => Filtrable (Sum f g) where
    mapMaybe f (InL as) = InL (mapMaybe f as)
    mapMaybe f (InR bs) = InR (mapMaybe f bs)

instance (Functor f, Filtrable g) => Filtrable (Compose f g) where
    mapMaybe f (Compose as) = Compose (mapMaybe f <$> as)

infixl 4 <$?>, <*?>

(<$?>) :: Filtrable f => (a -> Maybe b) -> f a -> f b
(<$?>) = mapMaybe

(<*?>) :: (Applicative p, Filtrable p) => p (a -> Maybe b) -> p a -> p b
f <*?> a = catMaybes (f <*> a)

nub :: (Filtrable f, Traversable f, Eq a) => f a -> f a
nub = nubBy (==)

nubBy :: (Filtrable f, Traversable f) => (a -> a -> Bool) -> f a -> f a
nubBy eq = fmap (flip M.evalState []) . filterA $ \ a -> do
    as <- M.get
    let b = all (not . eq a) as
    b <$ when b (M.modify (a:))

nubOrd :: (Filtrable f, Traversable f, Ord a) => f a -> f a
nubOrd = nubOrdBy compare

nubOrdBy :: (Filtrable f, Traversable f) => (a -> a -> Ordering) -> f a -> f a
nubOrdBy compare = fmap (flip M.evalState Set.empty) . filterA $ \ a -> M.state $ \ as ->
    case Set.insertBy' compare a as of
        Nothing -> (False, as)
        Just as' -> (True, as')
