{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies #-}
module Joy.Automata (
                     Automaton(..),
                     DFA,
                     NFA,
                    )
    where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import Joy.Uniqueness


class (Ord input) => Automaton fa input data' | fa -> input, fa -> data' where
    emptyAutomaton :: (MonadUnique m) => data' -> m fa
    automatonAddState :: (MonadUnique m) => fa -> data' -> m (fa, UniqueID)
    automatonAddTransition :: fa -> UniqueID -> UniqueID -> input -> fa
    automatonTransitionMap :: fa -> UniqueID -> Map input (Set UniqueID)
    automatonAccepting :: fa -> UniqueID -> Bool
    automatonSetAccepting :: fa -> UniqueID -> Bool -> fa
    automatonData :: fa -> UniqueID -> data'
    automatonSetData :: fa -> UniqueID -> data' -> fa
    automatonStates :: fa -> [UniqueID]


data DFA input data' = DFA (Map UniqueID (DFAState input data'))
                           UniqueID


data DFAState input data' = DFAState {
      dfaStateID :: UniqueID,
      dfaStateAccepting :: Bool,
      dfaStateSuccessors :: Map input UniqueID,
      dfaStateData :: data'
    }


instance (Ord input) => Automaton (DFA input data') input data' where
    emptyAutomaton datum = do
      startStateID <- getUniqueID
      let startState = DFAState {
                         dfaStateID = startStateID,
                         dfaStateAccepting = False,
                         dfaStateSuccessors = Map.empty,
                         dfaStateData = datum
                       }
      return $ DFA (Map.fromList [(startStateID, startState)]) startStateID
    automatonAddState (DFA stateMap startStateID) datum = do
      newStateID <- getUniqueID
      let newState = DFAState {
                       dfaStateID = newStateID,
                       dfaStateAccepting = False,
                       dfaStateSuccessors = Map.empty,
                       dfaStateData = datum
                     }
      return (DFA (Map.insert newStateID newState stateMap) startStateID, newStateID)
    automatonAddTransition (DFA stateMap startStateID) fromStateID toStateID input
        = let oldFromState = fromJust $ Map.lookup fromStateID stateMap
              oldSuccessors = dfaStateSuccessors oldFromState
              newSuccessors = Map.insert input toStateID oldSuccessors
              newFromState = oldFromState { dfaStateSuccessors = newSuccessors }
          in DFA (Map.insert fromStateID newFromState stateMap) startStateID
    automatonTransitionMap (DFA stateMap _) stateID
        = Map.map (\successor -> Set.fromList [successor])
                  $ dfaStateSuccessors $ fromJust $ Map.lookup stateID stateMap
    automatonAccepting (DFA stateMap _) stateID
        = dfaStateAccepting $ fromJust $ Map.lookup stateID stateMap
    automatonSetAccepting (DFA stateMap startStateID) stateID accepting
        = let oldState = fromJust $ Map.lookup stateID stateMap
              newState = oldState { dfaStateAccepting = accepting }
          in DFA (Map.insert stateID newState stateMap) startStateID
    automatonData (DFA stateMap _) stateID
        = dfaStateData $ fromJust $ Map.lookup stateID stateMap
    automatonSetData (DFA stateMap startStateID) stateID datum
        = let oldState = fromJust $ Map.lookup stateID stateMap
              newState = oldState { dfaStateData = datum }
          in DFA (Map.insert stateID newState stateMap) startStateID
    automatonStates (DFA stateMap _) = Map.keys stateMap


data NFA input data' = NFA (Map UniqueID (NFAState input data'))
                           (Set UniqueID)


data NFAState input data' = NFAState {
      nfaStateID :: UniqueID,
      nfaStateAccepting :: Bool,
      nfaStateSuccessors :: Map input (Set UniqueID),
      nfaStateData :: data'
    }


instance (Ord input) => Automaton (NFA input data') input data' where
    emptyAutomaton datum = do
      startStateID <- getUniqueID
      let startState = NFAState {
                         nfaStateID = startStateID,
                         nfaStateAccepting = False,
                         nfaStateSuccessors = Map.empty,
                         nfaStateData = datum
                       }
      return $ NFA (Map.fromList [(startStateID, startState)])
                   (Set.fromList [startStateID])
    automatonAddState (NFA stateMap startStateID) datum = do
      newStateID <- getUniqueID
      let newState = NFAState {
                       nfaStateID = newStateID,
                       nfaStateAccepting = False,
                       nfaStateSuccessors = Map.empty,
                       nfaStateData = datum
                     }
      return (NFA (Map.insert newStateID newState stateMap) startStateID, newStateID)
    automatonAddTransition (NFA stateMap startStateID) fromStateID toStateID input
        = let oldFromState = fromJust $ Map.lookup fromStateID stateMap
              oldSuccessorMap = nfaStateSuccessors oldFromState
              oldSuccessorSet = maybe Set.empty id $ Map.lookup input oldSuccessorMap
              newSuccessorSet = Set.insert toStateID oldSuccessorSet
              newSuccessorMap = Map.insert input newSuccessorSet oldSuccessorMap
              newFromState = oldFromState { nfaStateSuccessors = newSuccessorMap }
          in NFA (Map.insert fromStateID newFromState stateMap) startStateID
    automatonTransitionMap (NFA stateMap _) stateID
        = nfaStateSuccessors $ fromJust $ Map.lookup stateID stateMap
    automatonAccepting (NFA stateMap _) stateID
        = nfaStateAccepting $ fromJust $ Map.lookup stateID stateMap
    automatonSetAccepting (NFA stateMap startStateID) stateID accepting
        = let oldState = fromJust $ Map.lookup stateID stateMap
              newState = oldState { nfaStateAccepting = accepting }
          in NFA (Map.insert stateID newState stateMap) startStateID
    automatonData (NFA stateMap _) stateID
        = nfaStateData $ fromJust $ Map.lookup stateID stateMap
    automatonSetData (NFA stateMap startStateID) stateID datum
        = let oldState = fromJust $ Map.lookup stateID stateMap
              newState = oldState { nfaStateData = datum }
          in NFA (Map.insert stateID newState stateMap) startStateID
    automatonStates (NFA stateMap _) = Map.keys stateMap
