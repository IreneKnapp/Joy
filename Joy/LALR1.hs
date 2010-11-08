module Joy.LALR1 (
                  Production(..),
                  Item(..),
                  ProductionID(..),
                  StateID(..),
                  ParseTable(..),
                  compileParseTable
                 )
    where

import Control.Monad.Error
import Control.Monad.Identity
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Word

import Joy.Client
import Joy.Specification (GrammarSymbol(..))
import Joy.Uniqueness

import Debug.Trace


data Production = Production GrammarSymbol [GrammarSymbol] ClientAction
instance Eq Production where
  (==) (Production leftHandSideA rightHandSidesA _)
       (Production leftHandSideB rightHandSidesB _)
         = (==) (leftHandSideA, rightHandSidesA)
                (leftHandSideB, rightHandSidesB)
instance Ord Production where
  compare (Production leftHandSideA rightHandSidesA _)
          (Production leftHandSideB rightHandSidesB _)
         = compare (leftHandSideA, rightHandSidesA)
                   (leftHandSideB, rightHandSidesB)
instance Show Production where
  show (Production leftHandSide rightHandSides _)
    = (show leftHandSide)
      ++ " -> "
      ++ (intercalate " " $ map show rightHandSides)


data Item = Item Production Int
            deriving (Eq, Ord)
instance Show Item where
  show (Item (Production leftHandSide rightHandSides _) index)
    = (show leftHandSide)
      ++ " -> "
      ++ (intercalate " "
            $ let shownItems = map show rightHandSides
              in (take index shownItems) ++ ["."] ++ (drop index shownItems))


type ProductionID = Word64


type StateID = Word64


data InternalParseAction = InternalShift (Set Item)
                         | InternalReduce Production
                           deriving (Show)


data ParseAction = Shift StateID
                 | Reduce ProductionID
                   deriving (Show)


data ParseTable = ParseTable (Map GrammarSymbol StateID)
                             (Map StateID (Map GrammarSymbol [ParseAction]))
                  deriving (Show)


compileParseTable :: [GrammarSymbol]
                  -> [GrammarSymbol]
                  -> [Production]
                  -> [GrammarSymbol]
                  -> (ParseTable,
                      Map StateID (Set Item),
                      Map ProductionID Production)
compileParseTable nonterminals terminals allProductions startSymbols =
  let productionIDMap :: Map Production ProductionID
      productionIDMap = Map.fromList $ zip allProductions [0..]
      
      productionID :: Production -> ProductionID
      productionID production
        = fromJust $ Map.lookup production productionIDMap
      
      idProductionMap :: Map ProductionID Production
      idProductionMap = Map.fromList $ zip [0..] allProductions
      
      computeProductionsOfSymbol :: GrammarSymbol -> [Production]
      computeProductionsOfSymbol leftHandSymbol =
        filter (\(Production foundSymbol _ _) -> leftHandSymbol == foundSymbol)
               allProductions
      
      productionsOfSymbolMap :: Map GrammarSymbol [Production]
      productionsOfSymbolMap
        = Map.fromList
          $ map (\symbol -> (symbol, computeProductionsOfSymbol symbol))
                (nonterminals ++ terminals)
      
      productionsOfSymbol :: GrammarSymbol -> [Production]
      productionsOfSymbol symbol
        = fromJust $ Map.lookup symbol productionsOfSymbolMap
      
      computeSymbolNullable :: GrammarSymbol -> Set GrammarSymbol -> Bool
      computeSymbolNullable symbol@(Nonterminal _) visited =
        any (\(Production _ rightHandSymbols _) ->
               all (\rightHandSymbol ->
                      and [not $ Set.member rightHandSymbol visited,
                           computeSymbolNullable rightHandSymbol
                                                 $ Set.insert symbol visited])
                   rightHandSymbols)
            $ productionsOfSymbol symbol
      computeSymbolNullable _ _ = False
      
      symbolNullableMap :: Map GrammarSymbol Bool
      symbolNullableMap
        = Map.fromList
          $ map (\symbol -> (symbol, computeSymbolNullable symbol Set.empty))
                $ nonterminals ++ terminals
      
      symbolNullable :: GrammarSymbol -> Bool
      symbolNullable symbol
        = fromJust $ Map.lookup symbol symbolNullableMap
      
      computeLR0ParseTable :: (Map GrammarSymbol (Set Item),
                               [(Set Item,
                                 Map GrammarSymbol [InternalParseAction])])
      computeLR0ParseTable =
        let loop [] _ resultSoFar = resultSoFar
            loop (state:rest) visitedStates resultSoFar =
              let transitionMap
                    = Map.fromList
                      $ map (\symbol -> (symbol, computeNextState state symbol))
                            (nonterminals ++ terminals)
                  shiftActionMap
                    = Map.map (\maybeNextState ->
                                 case maybeNextState of
                                   Nothing -> []
                                   Just nextState -> [InternalShift nextState])
                              transitionMap
                  reduceActions
                    = map (\(Item production _) -> InternalReduce production)
                          $ filter (\(Item (Production _ rightHandSide _) index) ->
                                      index == length rightHandSide)
                                   $ Set.elems state
                  actionMap
                    = Map.map (\shiftActions -> shiftActions ++ reduceActions)
                              shiftActionMap
                  newStates = Set.fromList $ catMaybes $ Map.elems transitionMap
                  newStatesToVisit
                    = Set.elems $ Set.difference newStates visitedStates
                  visitedStates' = Set.insert state visitedStates
                  resultSoFar' = resultSoFar ++ [(state, actionMap)]
              in loop (rest ++ newStatesToVisit)
                      visitedStates'
                      resultSoFar'
            startStateMap = computeStartStateMap
            startStates = Map.elems startStateMap
        in (startStateMap,
            loop startStates Set.empty [])
      
      computeStartStateMap :: Map GrammarSymbol (Set Item)
      computeStartStateMap =
        Map.fromList
        $ catMaybes
        $ map (\symbol ->
                 let productions = productionsOfSymbol symbol
                     items = map (\production -> Item production 0) productions
                 in fmap (\state -> (symbol, state))
                         $ computeItemsClosure items)
              startSymbols
      
      computeNextState :: Set Item -> GrammarSymbol -> Maybe (Set Item)
      computeNextState state symbol =
        computeItemsClosure
         $ computeItemsAfterAdvancingSymbol (Set.elems state) symbol
      
      computeItemsAfterAdvancingSymbol :: [Item] -> GrammarSymbol -> [Item]
      computeItemsAfterAdvancingSymbol items symbol =
        concat
         $ map (\(Item production@(Production _ rightHandSide _) index) ->
                  if (index < length rightHandSide)
                     && ((head $ drop index rightHandSide) == symbol)
                    then [Item production (index + 1)]
                    else [])
               items
      
      computeItemsClosure :: [Item] -> Maybe (Set Item)
      computeItemsClosure items =
        let loop [] visitedItems resultSoFar = resultSoFar
            loop (item@(Item production@(Production leftHandSide
                                                    rightHandSides
                                                    _)
                             index)
                  : rest)
                 visitedItems
                 resultSoFar
              = let maybeNextSymbol =
                      if index < length rightHandSides
                        then Just $ head $ drop index rightHandSides
                        else Nothing
                    newItemsByLookingInside =
                      case maybeNextSymbol of
                        Nothing -> []
                        Just nextSymbol -> map (\production -> Item production 0)
                                               $ productionsOfSymbol nextSymbol
                    newItems = Set.fromList newItemsByLookingInside
                    newItemsToVisit
                      = Set.elems $ Set.difference newItems visitedItems
                    visitedItems' = Set.union newItems visitedItems
                    resultSoFar' = Set.union newItems resultSoFar
                in loop (rest ++ newItemsToVisit) visitedItems' resultSoFar'
            result = loop items Set.empty $ Set.fromList items
        in if Set.null result
           then Nothing
           else Just result
      
      computeLALR1ParseTable :: (ParseTable,
                                 Map StateID (Set Item),
                                 Map ProductionID Production)
      computeLALR1ParseTable =
        let (lr0ParseTable, stateDebugInfo, productionDebugInfo)
              = externalizeParseTable computeLR0ParseTable
            directReadSetMap = computeDirectReadSetMap lr0ParseTable
            nonterminalReadListMap = computeNonterminalReadListMap lr0ParseTable
            nonterminalTransitionSet
              = computeNonterminalTransitionSet lr0ParseTable
                {-
            readSetMap = digraph nonterminalTransitionSet
                                 directReadSetMap
                                 nonterminalReadListMap
                                 -}
        in (lr0ParseTable, stateDebugInfo, productionDebugInfo)
      
      computeDirectReadSetMap :: ParseTable
                              -> Map (StateID, GrammarSymbol)
                                     (Set GrammarSymbol)
      computeDirectReadSetMap (ParseTable _ transitionMap) =
        let computeDirectReadSet :: StateID -> GrammarSymbol -> Set GrammarSymbol
            computeDirectReadSet state nonterminal =
              case computeMaybeResultingState state nonterminal of
                Nothing -> Set.empty
                Just resultingState ->
                  Set.fromList $ map fst
                                     $ filter transitionIsTerminalShift
                                              $ Map.toList
                                                $ fromJust
                                                  $ Map.lookup resultingState
                                                               transitionMap
            
            transitionIsTerminalShift :: (GrammarSymbol, [ParseAction])
                                      -> Bool
            transitionIsTerminalShift (foundSymbol, actionList) =
              let isTerminal = case foundSymbol of
                                 Nonterminal _ -> False
                                 IdentifierTerminal _ -> True
                                 StringTerminal _ -> True
                  isShift = any (\action -> case action of
                                              Shift _ -> True
                                              Reduce _ -> False)
                                actionList
              in isTerminal && isShift
            
            computeMaybeResultingState :: StateID -> GrammarSymbol -> Maybe StateID
            computeMaybeResultingState state nonterminal =
              let maybeActionList =
                    Map.lookup nonterminal
                               $ fromJust $ Map.lookup state transitionMap
              in case maybeActionList of
                   Nothing -> Nothing
                   Just actionList ->
                     foldl (\maybeResult action ->
                              case maybeResult of
                                Nothing -> case action of
                                             Shift result -> Just result
                                             _ -> Nothing
                                Just result -> Just result)
                           Nothing
                           actionList
        
        in Map.fromList
           $ concat
           $ map (\state ->
                    map (\nonterminal ->
                           ((state, nonterminal),
                            computeDirectReadSet state nonterminal))
                        nonterminals)
                 $ Map.keys transitionMap
      
      computeNonterminalReadListMap :: ParseTable
                                    -> Map (StateID, GrammarSymbol)
                                           [(StateID, GrammarSymbol)]
      computeNonterminalReadListMap (ParseTable _ transitionMap) =
        let computeNonterminalReadList :: StateID
                                       -> GrammarSymbol
                                       -> [(StateID, GrammarSymbol)]
            computeNonterminalReadList state nonterminal =
              case computeMaybeResultingState state nonterminal of
                Nothing -> []
                Just resultingState ->
                  map (\(foundNonterminal, _) -> (resultingState, foundNonterminal))
                      $ filter transitionIsEpsilonNonterminalShift
                               $ Map.toList
                                 $ fromJust
                                   $ Map.lookup resultingState
                                                transitionMap
            
            transitionIsEpsilonNonterminalShift :: (GrammarSymbol, [ParseAction])
                                                -> Bool
            transitionIsEpsilonNonterminalShift (foundSymbol, actionList) =
              let isEpsilonNonterminal = symbolNullable foundSymbol
                  isShift = any (\action -> case action of
                                              Shift _ -> True
                                              Reduce _ -> False)
                                actionList
              in isEpsilonNonterminal && isShift
            
            computeMaybeResultingState :: StateID -> GrammarSymbol -> Maybe StateID
            computeMaybeResultingState state nonterminal =
              let maybeActionList =
                    Map.lookup nonterminal
                               $ fromJust $ Map.lookup state transitionMap
              in case maybeActionList of
                   Nothing -> Nothing
                   Just actionList ->
                     foldl (\maybeResult action ->
                              case maybeResult of
                                Nothing -> case action of
                                             Shift result -> Just result
                                             _ -> Nothing
                                Just result -> Just result)
                           Nothing
                           actionList
            
        in Map.fromList
           $ concat
           $ map (\state ->
                    map (\nonterminal ->
                           ((state, nonterminal),
                            computeNonterminalReadList state nonterminal))
                        nonterminals)
                 $ Map.keys transitionMap
      
      computeNonterminalTransitionSet :: ParseTable
                                      -> Set (StateID, GrammarSymbol)
      computeNonterminalTransitionSet (ParseTable _ transitionMap) =
        let transitionIsShift :: (StateID, GrammarSymbol) -> Bool
            transitionIsShift (state, nonterminal) =
              let actionListMap = fromJust $ Map.lookup state transitionMap
                  actionList = case Map.lookup nonterminal actionListMap of
                                 Nothing -> []
                                 Just actionList -> actionList
              in any (\action -> case action of
                                   Shift _ -> True
                                   Reduce _ -> False)
                     actionList
        in Set.fromList
           $ filter transitionIsShift
                    $ concat
                    $ map (\(state, actionListMap) ->
                             map (\nonterminal -> (state, nonterminal))
                                 $ Map.keys actionListMap)
                          $ Map.toList transitionMap
      
      externalizeParseTable :: (Map GrammarSymbol (Set Item),
                                [(Set Item,
                                  Map GrammarSymbol [InternalParseAction])])
                            -> (ParseTable,
                                Map StateID (Set Item),
                                Map ProductionID Production)
      externalizeParseTable (startStateMap, transitionMap) =
        let allStates = map fst transitionMap
            stateIDMap = Map.fromList $ zip allStates [0..]
            stateID state = fromJust $ Map.lookup state stateIDMap
            idStateMap = Map.fromList $ zip [0..] allStates
        in (ParseTable
             (Map.map stateID startStateMap)
             $ Map.fromList
             $ map (\(state, actionMap) ->
                      (stateID state,
                       Map.map (map (\action ->
                                       case action of
                                         InternalShift state -> Shift $ stateID state
                                         InternalReduce production
                                           -> Reduce $ productionID production))
                               actionMap))
                   transitionMap,
            idStateMap,
            idProductionMap)
      
  in computeLALR1ParseTable


{-
digraph :: Set (StateID, GrammarSymbol)
        -> Map (StateID, GrammarSymbol) (Set GrammarSymbol)
        -> Map (StateID, GrammarSymbol) [(StateID, GrammarSymbol)]
        -> Map (StateID, GrammarSymbol) (Set GrammarSymbol)
-}