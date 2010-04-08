{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, OverlappingInstances,
             UndecidableInstances, FlexibleContexts #-}
module Joy.Uniqueness (
                       UniqueID,
                       UniqueState,
                       MonadUnique(..),
                       UniqueT,
                       runUniqueT,
                       reenterUniqueT
                      )
    where

import Control.Monad.State
import Data.Word


type UniqueID = Word64
type UniqueState = UniqueID


class (Monad m) => MonadUnique m where
    getUniqueID :: m UniqueID
    getUniqueState :: m UniqueState


type UniqueT = StateT UniqueID


instance (Monad m) => MonadUnique (UniqueT m) where
    getUniqueID = do
      uniqueID <- get
      put $ uniqueID + 1
      return uniqueID
    getUniqueState = get


instance (MonadTrans t, Monad (t m), MonadUnique m) => MonadUnique (t m) where
    getUniqueID = lift getUniqueID
    getUniqueState = lift getUniqueState


runUniqueT :: (Monad m) => (UniqueT m a) -> m a
runUniqueT action = evalStateT action 0


reenterUniqueT :: (Monad m) => UniqueState -> (UniqueT m a) -> m a
reenterUniqueT state action = evalStateT action state
