{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, OverlappingInstances,
             UndecidableInstances, FlexibleContexts #-}
module Joy.Uniqueness (
                       UniqueID,
                       MonadUnique(..),
                       UniqueT,
                       runUniqueT
                      )
    where

import Control.Monad.State
import Data.Word


type UniqueID = Word64


class (Monad m) => MonadUnique m where
    getUniqueID :: m UniqueID


type UniqueT = StateT UniqueID


instance (Monad m) => MonadUnique (UniqueT m) where
    getUniqueID = do
      uniqueID <- get
      put $ uniqueID + 1
      return uniqueID


instance (MonadTrans t, Monad (t m), MonadUnique m) => MonadUnique (t m) where
    getUniqueID = lift getUniqueID


runUniqueT :: (Monad m) => (UniqueT m a) -> m a
runUniqueT action = evalStateT action 0
