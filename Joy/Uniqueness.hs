{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, OverlappingInstances,
             UndecidableInstances, FlexibleContexts #-}
module Joy.Uniqueness (
                       UniqueID,
                       UniquenessPurpose,
                       UniqueState,
                       MonadUnique(getUniqueID, getUniqueIDForPurpose),
                       withUniquenessPurpose,
                       UniqueT,
                       runUniqueT
                      )
    where

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Word

import Joy.Suspendability


type UniqueID = Word64
type UniquenessPurpose = UniqueID
data UniqueState = UniqueState {
    generalPurposeUniqueness :: UniqueID,
    specialPurposeUniqueness :: Map UniquenessPurpose UniqueID
  }


class (Monad m) => MonadUnique m where
    getUniqueID :: m UniqueID
    createUniquenessPurpose :: m UniquenessPurpose
    deleteUniquenessPurpose :: UniquenessPurpose -> m ()
    getUniqueIDForPurpose :: UniquenessPurpose -> m UniqueID


withUniquenessPurpose :: (MonadUnique m,
                          SuspendableMonad m state error (),
                          SuspendableMonad m state error UniquenessPurpose,
                          SuspendableMonad m state error a,
                          MonadIO m)
                         => (UniquenessPurpose -> m a) -> m a
withUniquenessPurpose =
  bracket createUniquenessPurpose
          deleteUniquenessPurpose


type UniqueT = StateT UniqueState


instance (Monad m) => MonadUnique (UniqueT m) where
    getUniqueID = do
      state <- get
      let uniqueID = generalPurposeUniqueness state
      put $ state { generalPurposeUniqueness = uniqueID + 1 }
      return uniqueID
    createUniquenessPurpose = do
      purpose <- getUniqueID
      state <- get
      let purposeMap = specialPurposeUniqueness state
      put $ state { specialPurposeUniqueness = Map.insert purpose 0 purposeMap }
      return purpose
    deleteUniquenessPurpose purpose = do
      state <- get
      let purposeMap = specialPurposeUniqueness state
      put $ state { specialPurposeUniqueness = Map.delete purpose purposeMap }
    getUniqueIDForPurpose purpose = do
      state <- get
      let purposeMap = specialPurposeUniqueness state
      case Map.lookup purpose purposeMap of
        Nothing -> error "Unknown uniqueness purpose."
        Just uniqueID -> do
          put $ state { specialPurposeUniqueness = Map.insert purpose
                                                              (uniqueID + 1)
                                                              purposeMap }
          return uniqueID


instance (MonadTrans t, Monad (t m), MonadUnique m) => MonadUnique (t m) where
    getUniqueID = lift getUniqueID
    createUniquenessPurpose = lift createUniquenessPurpose
    deleteUniquenessPurpose purpose = lift $ deleteUniquenessPurpose purpose
    getUniqueIDForPurpose purpose = lift $ getUniqueIDForPurpose purpose


runUniqueT :: (Monad m) => (UniqueT m a) -> m a
runUniqueT action = evalStateT action $ UniqueState {
                      generalPurposeUniqueness = 0,
                      specialPurposeUniqueness = Map.empty
                    }
