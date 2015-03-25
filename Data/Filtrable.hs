module Data.Filtrable where

import Prelude hiding (filter)

import Control.Applicative
import Control.Monad
import Data.Proxy
import Data.Traversable

class Functor f => Filtrable f where
    {-# MINIMAL mapMaybe | catMaybes #-}

    mapMaybe :: (a -> Maybe b) -> f a -> f b
    mapMaybe f = catMaybes . fmap f

    catMaybes :: f (Maybe a) -> f a
    catMaybes = mapMaybe id

    filter :: (a -> Bool) -> f a -> f a
    filter f = mapMaybe (liftA2 (<$) id (guard . f))

instance Filtrable [] where
    mapMaybe f = foldr (maybe id (:) . f) []

instance Filtrable Maybe where
    mapMaybe = (=<<)
    catMaybes = join

instance Filtrable Proxy where
    mapMaybe _ Proxy = Proxy

instance Filtrable (Const a) where
    mapMaybe _ (Const x) = Const x

mapMaybeA :: (Filtrable f, Traversable f, Applicative p) => (a -> p (Maybe b)) -> f a -> p (f b)
mapMaybeA f xs = catMaybes <$> traverse f xs

filterA :: (Filtrable f, Traversable f, Applicative p) => (a -> p Bool) -> f a -> p (f a)
filterA f = mapMaybeA (\ x -> (x <$) . guard <$> f x)
