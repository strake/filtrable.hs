module Data.Filtrable (Filtrable (..)) where

import Prelude hiding (filter)

import Control.Applicative
import Control.Monad
import Data.Bool (bool)
import Data.Proxy
import Data.Traversable

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
