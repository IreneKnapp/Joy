{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies,
             ScopedTypeVariables #-}
module Joy.Automata (
                     Automaton(..),
                     DFA,
                     dfaStartState,
                     NFA,
                     nfaStartSet,
                     combineNFAs,
                     nfaToDFA
                    )
    where

import Control.Monad.Error
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import Joy.EnumSet
import Joy.Uniqueness


class (Ord input) => Automaton fa input stateData transitionData
    | fa -> input, fa -> stateData, fa -> transitionData where
    emptyAutomaton :: (MonadUnique m) => stateData -> m fa
    automatonAddState :: (MonadUnique m) => fa -> stateData -> m (fa, UniqueID)
    automatonAddTransition
        :: fa -> UniqueID -> UniqueID -> input -> transitionData -> fa
    automatonTransitionMap
        :: fa -> UniqueID -> Map input [(UniqueID, transitionData)]
    automatonStateStarting :: fa -> UniqueID -> Bool
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
    automatonStateStarting (DFA _ startID) stateID
        = startID == stateID
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


dfaStartState :: (DFA input stateData transitionData) -> UniqueID
dfaStartState (DFA _ startState) = startState


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
    automatonStateStarting (NFA _ startSet) stateID
        = Set.member stateID startSet
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


nfaStartSet :: (NFA input stateData transitionData) -> Set UniqueID
nfaStartSet (NFA _ startSet) = startSet


combineNFAs :: [NFA input stateData transitionData] -> NFA input stateData transitionData
combineNFAs inputs = NFA (Map.unions $ map (\(NFA stateMap _) -> stateMap) inputs)
                         (Set.unions $ map (\(NFA _ startSet) -> startSet) inputs)


data AutomatonConversionError = AutomatonConversionError String
instance Error AutomatonConversionError where
    strMsg string = AutomatonConversionError string


nfaToDFA :: forall m content stateData transitionData .
            (MonadUnique m, Ord content, Bounded content, Enum content)
         => (NFA (EnumSet content) (Maybe stateData) transitionData)
         -> m (Either String (DFA (EnumSet content) (Maybe stateData) ()))
nfaToDFA nfa = do
    let convertQueue :: [Set UniqueID]
                     -> (DFA (EnumSet content) (Maybe stateData) ())
                     -> (Map (Set UniqueID) UniqueID)
                     -> ErrorT AutomatonConversionError m
                        (DFA (EnumSet content) (Maybe stateData) ())
        convertQueue [] dfa _ = return dfa
        convertQueue ((sourceNFAStates):queue) dfa stateSetMap = do
          let sourceDFAState = fromJust $ Map.lookup sourceNFAStates stateSetMap
              relevantEnumSets
                  = relevantSubsetsForEnumSets
                    $ concat
                    $ map (\state -> Map.keys $ automatonTransitionMap nfa state)
                    $ Set.toList
                    sourceNFAStates
          (dfa, stateSetMap, queue)
              <- foldM
                 (\(dfa, stateSetMap, queue) enumSet -> do
                   let testInput = fromJust $ anyEnumInSet enumSet
                       targetNFAStates
                           = Set.fromList
                             $ nub
                             $ concat
                             $ map
                               (\sourceNFAState ->
                                 map fst
                                 $ fromJust
                                 $ getTransition nfa sourceNFAState testInput)
                               $ Set.toList sourceNFAStates
                   if Set.size targetNFAStates > 0
                     then do
                       (dfa, targetDFAState)
                           <- case Map.lookup targetNFAStates stateSetMap of
                                Just targetDFAState -> do
                                  dfa <- return $ automatonAddTransition dfa
                                                                         sourceDFAState
                                                                         targetDFAState
                                                                         enumSet
                                                                         ()
                                  return (dfa, targetDFAState)
                                Nothing -> do
                                  let possibleActions
                                        = foldl (\accumulator maybeAction ->
                                                  case maybeAction of
                                                    Nothing -> accumulator
                                                    Just action -> accumulator
                                                                   ++ [action])
                                                []
                                                $ map (\state
                                                        -> automatonStateData nfa state)
                                                      $ Set.toList targetNFAStates
                                  maybeAction
                                      <- case possibleActions of
                                           [] -> return Nothing
                                           [action] -> return $ Just action
                                           _ -> fail $ "Conflict in lexer"
                                  let accepting = any (automatonStateAccepting nfa)
                                                      $ Set.toList targetNFAStates
                                  (dfa, targetDFAState) <- automatonAddState dfa
                                                                             maybeAction
                                  dfa <- return $ automatonSetStateAccepting
                                                    dfa
                                                    targetDFAState
                                                    accepting
                                  dfa <- return $ automatonAddTransition dfa
                                                                         sourceDFAState
                                                                         targetDFAState
                                                                         enumSet
                                                                         ()
                                  return (dfa, targetDFAState)
                       stateSetMap <- return $ Map.insert targetNFAStates
                                                          targetDFAState
                                                          stateSetMap
                       queue <- return $ enqueue queue stateSetMap targetNFAStates
                       return (dfa, stateSetMap, queue)
                     else return (dfa, stateSetMap, queue))
                (dfa, stateSetMap, queue)
                relevantEnumSets
          convertQueue queue dfa stateSetMap
        
        enqueue :: [Set UniqueID]
                -> (Map (Set UniqueID) UniqueID)
                -> (Set UniqueID)
                -> [Set UniqueID]
        enqueue queue stateSetMap newNFAStateSet =
            if (elem newNFAStateSet queue)
               || (isJust $ Map.lookup newNFAStateSet stateSetMap)
              then queue
              else queue ++ [newNFAStateSet]
        
        getTransition :: (NFA (EnumSet content) (Maybe stateData) transitionData)
                      -> UniqueID
                      -> content
                      -> (Maybe [(UniqueID, transitionData)])
        getTransition nfa sourceState input =
          foldl (\maybeCumulativeResult (enumSet, transitionResult) ->
                  let partialResult = if enumInSet enumSet input
                                        then transitionResult
                                        else []
                  in case maybeCumulativeResult of
                       Just cumulativeResult -> Just $ cumulativeResult ++ partialResult
                       Nothing -> Just partialResult)
                Nothing
                $ Map.toList $ automatonTransitionMap nfa sourceState
        
        convertAll :: ErrorT AutomatonConversionError m
                      (DFA (EnumSet content) (Maybe stateData) ())
        convertAll = do
          dfa <- emptyAutomaton Nothing
          convertQueue [nfaStartSet nfa]
                       dfa
                       $ Map.fromList [(nfaStartSet nfa, dfaStartState dfa)]
        
    result <- runErrorT convertAll
    return $ case result of
      Left (AutomatonConversionError message) -> Left message
      Right result -> Right result
