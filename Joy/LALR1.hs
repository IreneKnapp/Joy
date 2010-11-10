module Joy.LALR1 (
                  Production(..),
                  Item(..),
                  ProductionID(..),
                  StateID(..),
                  ParseTable(..),
                  compileParseTable
                 )
    where

import Control.Monad.State
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
                               Map (Set Item)
                                   (Map GrammarSymbol [InternalParseAction]))
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
            Map.fromList $ loop startStates Set.empty [])
      
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
            nonterminalReadSetMap = computeNonterminalReadSetMap lr0ParseTable
            nonterminalTransitionSet
              = computeNonterminalTransitionSet lr0ParseTable
            readSetMap = digraph nonterminalTransitionSet
                                 nonterminalReadSetMap
                                 directReadSetMap
            (includesSetMap, lookbackSetMap) =
              computeIncludesAndLookbackSetMaps lr0ParseTable
            followSetMap = digraph nonterminalTransitionSet
                                   includesSetMap
                                   readSetMap
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
      
      computeNonterminalReadSetMap :: ParseTable
                                    -> Map (StateID, GrammarSymbol)
                                           (Set (StateID, GrammarSymbol))
      computeNonterminalReadSetMap (ParseTable _ transitionMap) =
        let computeNonterminalReadSet :: StateID
                                      -> GrammarSymbol
                                      -> (Set (StateID, GrammarSymbol))
            computeNonterminalReadSet state nonterminal =
              case computeMaybeResultingState state nonterminal of
                Nothing -> Set.empty
                Just resultingState ->
                  Set.fromList
                  $ map (\(foundNonterminal, _) ->
                           (resultingState, foundNonterminal))
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
                            computeNonterminalReadSet state nonterminal))
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
      
      computeIncludesAndLookbackSetMaps
        :: ParseTable
        -> (Map (StateID, GrammarSymbol)
                (Set (StateID, GrammarSymbol)),
            Map (StateID, ProductionID)
                (Set (StateID, GrammarSymbol)))
      computeIncludesAndLookbackSetMaps (ParseTable _ transitionMap) =
        let combineResults
              :: [(Map (StateID, GrammarSymbol)
                       (Set (StateID, GrammarSymbol)),
                   Map (StateID, ProductionID)
                       (Set (StateID, GrammarSymbol)))]
              -> (Map (StateID, GrammarSymbol)
                      (Set (StateID, GrammarSymbol)),
                  Map (StateID, ProductionID)
                      (Set (StateID, GrammarSymbol)))
            combineResults results =
              (foldl (Map.unionWith Set.union) Map.empty $ map fst results,
               foldl (Map.unionWith Set.union) Map.empty $ map snd results)
            visitAll :: (Map (StateID, GrammarSymbol)
                             (Set (StateID, GrammarSymbol)),
                         Map (StateID, ProductionID)
                             (Set (StateID, GrammarSymbol)))
            visitAll =
              combineResults $ map visitState $ Map.keys transitionMap
            visitState :: StateID
                       -> (Map (StateID, GrammarSymbol)
                               (Set (StateID, GrammarSymbol)),
                           Map (StateID, ProductionID)
                               (Set (StateID, GrammarSymbol)))
            visitState state =
              combineResults $ map (visitNonterminal state) nonterminals
            visitNonterminal :: StateID
                             -> GrammarSymbol
                             -> (Map (StateID, GrammarSymbol)
                                     (Set (StateID, GrammarSymbol)),
                                 Map (StateID, ProductionID)
                                     (Set (StateID, GrammarSymbol)))
            visitNonterminal state nonterminal =
              let actionListMap = fromJust $ Map.lookup state transitionMap
                  actionList = case Map.lookup nonterminal actionListMap of
                                 Nothing -> []
                                 Just actionList -> actionList
                  isShift = any (\action -> case action of
                                              Shift _ -> True
                                              Reduce _ -> False)
                                actionList
              in if isShift
                   then combineResults $ map (visitProduction state nonterminal)
                                             $ productionsOfSymbol nonterminal
                   else (Map.empty, Map.empty)
            visitProduction :: StateID
                            -> GrammarSymbol
                            -> Production
                            -> (Map (StateID, GrammarSymbol)
                                    (Set (StateID, GrammarSymbol)),
                                Map (StateID, ProductionID)
                                    (Set (StateID, GrammarSymbol)))
            visitProduction state nonterminal production =
              let Production _ rightHandSides _ = production
                  (includeResults, foundState) =
                    foldl (\(includeResults, foundState) (foundSymbol, index) ->
                             let actionListMap
                                   = fromJust $ Map.lookup foundState
                                                           transitionMap
                                 actionList =
                                   case Map.lookup nonterminal actionListMap of
                                     Nothing -> []
                                     Just actionList -> actionList
                                 maybeFoundState' =
                                   foldl (\maybeResult action ->
                                            case maybeResult of
                                              Just _ -> maybeResult
                                              Nothing ->
                                                case action of
                                                  Shift result -> Just result
                                                  _ -> Nothing)
                                         Nothing
                                         actionList
                                 foundState' = case maybeFoundState' of
                                                 Just foundState' -> foundState'
                                                 Nothing -> foundState
                                 remainingSymbols =
                                   drop (index + 1) rightHandSides
                                 notInOriginalState =
                                   (state, nonterminal)
                                   /= (foundState, foundSymbol)
                                 remainderNullable
                                   = all symbolNullable remainingSymbols
                                 newIncludeResults =
                                   if notInOriginalState && remainderNullable
                                     then Map.singleton
                                           (foundState, foundSymbol)
                                           $ Set.singleton
                                              (state, nonterminal)
                                     else Map.empty
                                 includeResults' =
                                   Map.unionWith Set.union
                                                 includeResults
                                                 newIncludeResults
                             in case foundSymbol of
                                  Nonterminal _ -> (includeResults', foundState')
                                  _ -> (includeResults, foundState'))
                          (Map.empty, state)
                          $ zip rightHandSides [0..]
                  lookbackResults = Map.singleton
                                     (foundState, productionID production)
                                     $ Set.singleton (state, nonterminal) 
              in (includeResults, lookbackResults)
        in visitAll
      
      externalizeParseTable :: (Map GrammarSymbol (Set Item),
                                Map (Set Item)
                                    (Map GrammarSymbol [InternalParseAction]))
                            -> (ParseTable,
                                Map StateID (Set Item),
                                Map ProductionID Production)
      externalizeParseTable (startStateMap, transitionMap) =
        let allStates = Map.keys transitionMap
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
                   $ Map.toList transitionMap,
            idStateMap,
            idProductionMap)
      
  in computeLALR1ParseTable


data DigraphState item functionResult = DigraphState {
    digraphStateStack :: [item],
    digraphStateDepthMap :: Map item DigraphDepth,
    digraphStateOutputFunction :: Map item (Set functionResult)
  }
type Digraph item functionResult = State (DigraphState item functionResult)
data DigraphDepth = IntegralDepth Int
                  | InfiniteDepth
                    deriving (Eq)
instance Ord DigraphDepth where
  compare (IntegralDepth a) (IntegralDepth b) = compare a b
  compare (IntegralDepth _) InfiniteDepth = LT
  compare InfiniteDepth (IntegralDepth _) = GT
  compare InfiniteDepth InfiniteDepth = EQ


digraph :: (Ord item, Ord functionResult, Show item)
        => Set item
        -> Map item (Set item)
        -> Map item (Set functionResult)
        -> Map item (Set functionResult)
digraph set relation inputFunction =
  let traverseAll = do
        countRemaining
          <- foldM (\total item -> do
                      depth <- getItemDepth item
                      if depth == IntegralDepth 0
                        then do
                          traverse item
                          return $ total + 1
                        else return total)
                   0
                   $ Set.elems set
        if countRemaining > 0
          then traverseAll
          else return ()
      
      traverse item = do
        stackPush item
        depth <- getStackDepth
        setItemDepth item $ IntegralDepth depth
        assignOutputFunctionResults item
                                    $ case Map.lookup item inputFunction of
                                        Nothing -> Set.empty
                                        Just results -> results
        mapM_ (\otherItem -> do
                 otherDepth <- getItemDepth otherItem
                 if otherDepth == IntegralDepth 0
                   then traverse otherItem
                   else return ()
                 depth' <- getItemDepth item
                 otherDepth' <- getItemDepth otherItem
                 setItemDepth item $ min depth' otherDepth'
                 newResults <- getOutputFunctionResults otherItem
                 unionOutputFunctionResults item newResults)
              $ case Map.lookup item relation of
                  Just otherItemSet -> Set.elems otherItemSet
                  Nothing -> []
        depth' <- getItemDepth item
        if IntegralDepth depth == depth'
          then do
            itemResults <- getOutputFunctionResults item
            let loop = do
                  topItem <- stackPop
                  setItemDepth topItem InfiniteDepth
                  assignOutputFunctionResults topItem itemResults
                  if topItem == item
                    then return ()
                    else loop
            loop
          else return ()
      
      initialState = DigraphState {
                       digraphStateStack = [],
                       digraphStateDepthMap
                         = Map.fromList
                           $ map (\item -> (item, IntegralDepth 0))
                                 $ Set.elems set,
                       digraphStateOutputFunction = Map.empty
                     }
      
      stackPush item = do
        state@DigraphState { digraphStateStack = stack } <- get
        let stack' = item : stack
        put $ state { digraphStateStack = stack' }
      stackPop = do
        state@DigraphState { digraphStateStack = stack } <- get
        let (result : stack') = stack
        put $ state { digraphStateStack = stack' }
        return result
      getStackDepth = do
        DigraphState { digraphStateStack = stack } <- get
        return $ length stack
      
      getItemDepth item = do
        DigraphState { digraphStateDepthMap = depthMap } <- get
        return $ fromJust $ Map.lookup item depthMap
      setItemDepth item newDepth = do
        state@DigraphState { digraphStateDepthMap = depthMap } <- get
        let depthMap' = Map.insert item newDepth depthMap
        put $ state { digraphStateDepthMap = depthMap' }
      
      getInputFunctionResults item = do
        return $ case Map.lookup item inputFunction of
                   Nothing -> Set.empty
                   Just results -> results
      
      getOutputFunctionResults item = do
        DigraphState {
                      digraphStateOutputFunction = outputFunction
                    } <- get
        return $ case Map.lookup item outputFunction of
                   Nothing -> Set.empty
                   Just results -> results
      assignOutputFunctionResults item results = do
        state@DigraphState {
                      digraphStateOutputFunction = outputFunction
                    } <- get
        let outputFunction'
              = Map.insert item results outputFunction
        put $ state { digraphStateOutputFunction = outputFunction' }
      unionOutputFunctionResults item results = do
        state@DigraphState {
                      digraphStateOutputFunction = outputFunction
                    } <- get
        let outputFunction'
              = Map.insertWith Set.union item results outputFunction
        put $ state { digraphStateOutputFunction = outputFunction' }
  in digraphStateOutputFunction $ execState traverseAll initialState
