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


class (Ord input) => Automaton fa input stateData transitionData
    | fa -> input, fa -> stateData, fa -> transitionData where
    emptyAutomaton :: (MonadUnique m) => stateData -> m fa
    automatonAddState :: (MonadUnique m) => fa -> stateData -> m (fa, UniqueID)
    automatonAddTransition
        :: fa -> UniqueID -> UniqueID -> input -> transitionData -> fa
    automatonTransitionMap
        :: fa -> UniqueID -> Map input [(UniqueID, transitionData)]
    automatonStateAccepting :: fa -> UniqueID -> Bool
    automatonSetStateAccepting :: fa -> UniqueID -> Bool -> fa
    automatonStateData :: fa -> UniqueID -> stateData
    automatonSetStateData :: fa -> UniqueID -> stateData -> fa
    automatonStates :: fa -> [UniqueID]


data DFA input stateData transitionData
    = DFA (Map UniqueID (DFAState input stateData transitionData))
          UniqueID


data DFAState input stateData transitionData = DFAState {
      dfaStateID :: UniqueID,
      dfaStateAccepting :: Bool,
      dfaStateSuccessors :: Map input (UniqueID, transitionData),
      dfaStateData :: stateData
    }


instance (Ord input) => Automaton (DFA input stateData transitionData)
                                  input stateData transitionData where
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
    automatonAddTransition (DFA stateMap startStateID) fromStateID toStateID input datum
        = let oldFromState = fromJust $ Map.lookup fromStateID stateMap
              oldSuccessors = dfaStateSuccessors oldFromState
              newSuccessors = Map.insert input (toStateID, datum) oldSuccessors
              newFromState = oldFromState { dfaStateSuccessors = newSuccessors }
          in DFA (Map.insert fromStateID newFromState stateMap) startStateID
    automatonTransitionMap (DFA stateMap _) stateID
        = Map.map (\successor -> [successor])
                  $ dfaStateSuccessors $ fromJust $ Map.lookup stateID stateMap
    automatonStateAccepting (DFA stateMap _) stateID
        = dfaStateAccepting $ fromJust $ Map.lookup stateID stateMap
    automatonSetStateAccepting (DFA stateMap startStateID) stateID accepting
        = let oldState = fromJust $ Map.lookup stateID stateMap
              newState = oldState { dfaStateAccepting = accepting }
          in DFA (Map.insert stateID newState stateMap) startStateID
    automatonStateData (DFA stateMap _) stateID
        = dfaStateData $ fromJust $ Map.lookup stateID stateMap
    automatonSetStateData (DFA stateMap startStateID) stateID datum
        = let oldState = fromJust $ Map.lookup stateID stateMap
              newState = oldState { dfaStateData = datum }
          in DFA (Map.insert stateID newState stateMap) startStateID
    automatonStates (DFA stateMap _) = Map.keys stateMap


data NFA input stateData transitionData
    = NFA (Map UniqueID (NFAState input stateData transitionData))
          (Set UniqueID)


data NFAState input stateData transitionData = NFAState {
      nfaStateID :: UniqueID,
      nfaStateAccepting :: Bool,
      nfaStateSuccessors :: Map input [(UniqueID, transitionData)],
      nfaStateData :: stateData
    }


instance (Ord input) => Automaton (NFA input stateData transitionData)
                                  input stateData transitionData where
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
    automatonAddTransition (NFA stateMap startStateID) fromStateID toStateID input datum
        = let oldFromState = fromJust $ Map.lookup fromStateID stateMap
              oldSuccessorMap = nfaStateSuccessors oldFromState
              oldSuccessorSet = maybe [] id $ Map.lookup input oldSuccessorMap
              newSuccessorSet = oldSuccessorSet ++ [(toStateID, datum)]
              newSuccessorMap = Map.insert input newSuccessorSet oldSuccessorMap
              newFromState = oldFromState { nfaStateSuccessors = newSuccessorMap }
          in NFA (Map.insert fromStateID newFromState stateMap) startStateID
    automatonTransitionMap (NFA stateMap _) stateID
        = nfaStateSuccessors $ fromJust $ Map.lookup stateID stateMap
    automatonStateAccepting (NFA stateMap _) stateID
        = nfaStateAccepting $ fromJust $ Map.lookup stateID stateMap
    automatonSetStateAccepting (NFA stateMap startStateID) stateID accepting
        = let oldState = fromJust $ Map.lookup stateID stateMap
              newState = oldState { nfaStateAccepting = accepting }
          in NFA (Map.insert stateID newState stateMap) startStateID
    automatonStateData (NFA stateMap _) stateID
        = nfaStateData $ fromJust $ Map.lookup stateID stateMap
    automatonSetStateData (NFA stateMap startStateID) stateID datum
        = let oldState = fromJust $ Map.lookup stateID stateMap
              newState = oldState { nfaStateData = datum }
          in NFA (Map.insert stateID newState stateMap) startStateID
    automatonStates (NFA stateMap _) = Map.keys stateMap
