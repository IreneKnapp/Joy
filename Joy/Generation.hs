{-# LANGUAGE ExistentialQuantification, FlexibleContexts, FlexibleInstances,
             TypeSynonymInstances #-}
module Joy.Generation (
                       Generation(..),
                       GenerationError(..),
                       GenerationState(..),
                       LexerInformation(..),
                       Lexer(..),
                       AnyLexer(..),
                       ParserInformation(..),
                       Production(..),
                       mkGenerationState,
                       runGeneration,
                       generate
                      )
    where

import Control.Monad.Error
import Control.Monad.State
import Data.Char
import Data.Function
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Time
import Data.Time.Clock.POSIX
import Data.Word
import Numeric
import System.IO hiding (withFile)
import System.Locale

import Joy.Automata
import Joy.Client
import Joy.Documentation
import Joy.EnumSet (EnumSet)
import qualified Joy.EnumSet as EnumSet
import Joy.LALR1
import Joy.Uniqueness
import Joy.Regexp
import Joy.Specification
import Joy.Suspendability (withFile)


type Generation = ErrorT GenerationError (StateT GenerationState (UniqueT IO))


data GenerationError = GenerationError String
instance Error GenerationError where
    strMsg message = GenerationError message
instance Show GenerationError where
    show (GenerationError string) = string


data GenerationState = GenerationState {
        generationStateInputFilename :: FilePath,
        generationStateOutputFilename :: FilePath,
        generationStateMaybeSpecification :: Maybe Specification,
        generationStateMaybeMonadType :: Maybe ClientType,
        generationStateMaybeLexerInformation :: Maybe LexerInformation,
        generationStateMaybeErrorFunction :: Maybe ClientExpression,
        generationStateMaybeCompiledLexers :: Maybe [(String, Bool, AnyLexer)],
        generationStateMaybeTokenType :: Maybe ClientType,
        generationStateMaybeAnyParsersSpecified :: Maybe Bool,
        generationStateMaybeTerminals :: Maybe [GrammarSymbol],
        generationStateMaybeTerminalPatternMap :: Maybe (Map GrammarSymbol
                                                             ClientPattern),
        generationStateMaybePatternTerminalAlist :: Maybe [(ClientPattern,
                                                            GrammarSymbol)],
        generationStateMaybeNonterminals :: Maybe [GrammarSymbol],
        generationStateMaybeNonterminalTypeMap :: Maybe (Map GrammarSymbol
                                                             ClientType),
        generationStateMaybeProductions :: Maybe [Production],
        generationStateMaybeParserInformationMap
          :: Maybe (Map GrammarSymbol ParserInformation),
        generationStateMaybeParseTable :: Maybe ParseTable,
        generationStateMaybeParseTableStateDebugInfo
          :: Maybe (Map StateID (Set Item)),
        generationStateMaybeParseTableProductionDebugInfo
          :: Maybe (Map ProductionID Production)
      }


data LexerInformation = LexerInformation {
        lexerInformationInitialName :: String,
        lexerInformationUserNames :: [String],
        lexerInformationNonuserNamesAndDefinitions
            :: [(String, Bool, [LexerDefinitionItem])]
    }


type Lexer content = DFA (EnumSet content) (Maybe (Maybe ClientExpression)) ()


data AnyLexer = forall content . (Ord content, Bounded content, Enum content) =>
                Lexer (Lexer content)


data ParserInformation = ParserInformation {
    parserInformationGrammarSymbol :: GrammarSymbol,
    parserInformationPartial :: Bool,
    parserInformationClientIdentifier :: ClientIdentifier
  }


mkGenerationState :: FilePath -> FilePath -> GenerationState
mkGenerationState inputFilename outputFilename
    = GenerationState {
        generationStateInputFilename = inputFilename,
        generationStateOutputFilename = outputFilename,
        generationStateMaybeSpecification = Nothing,
        generationStateMaybeMonadType = Nothing,
        generationStateMaybeLexerInformation = Nothing,
        generationStateMaybeErrorFunction = Nothing,
        generationStateMaybeCompiledLexers = Nothing,
        generationStateMaybeTokenType = Nothing,
        generationStateMaybeAnyParsersSpecified = Nothing,
        generationStateMaybeTerminals = Nothing,
        generationStateMaybeTerminalPatternMap = Nothing,
        generationStateMaybePatternTerminalAlist = Nothing,
        generationStateMaybeNonterminals = Nothing,
        generationStateMaybeNonterminalTypeMap = Nothing,
        generationStateMaybeProductions = Nothing,
        generationStateMaybeParserInformationMap = Nothing,
        generationStateMaybeParseTable = Nothing,
        generationStateMaybeParseTableStateDebugInfo = Nothing,
        generationStateMaybeParseTableProductionDebugInfo = Nothing
      }


runGeneration :: (Generation a) -> GenerationState -> IO (Either GenerationError a)
runGeneration action state = runUniqueT $ flip evalStateT state $ runErrorT action


debugSpecification :: Generation ()
debugSpecification = do
  {-
  let visitDeclaration (declaration:rest) = do
        liftIO $ putStrLn $ show declaration
        visitDeclaration rest
      visitDeclaration [] = return ()
  GenerationState { generationStateSpecification = specification } <- get
  visitDeclaration $ specificationDeclarations specification
  -}
  return ()


debugEarlyGenerationState :: Generation ()
debugEarlyGenerationState = do
  {-
  state <- get
  liftIO $ do
    putStrLn $ "Monad type: "
               ++ (show $ generationStateMaybeMonadType state)
    putStrLn $ "Lexer information: "
               ++ (show $ generationStateMaybeLexerInformation state)
    putStrLn $ "Error function: "
               ++ (show $ generationStateMaybeErrorFunction state)
    putStrLn $ "Terminals: "
               ++ (show $ generationStateTerminals state)
    putStrLn $ "Nonterminals: "
               ++ (show $ generationStateNonterminals state)
    putStrLn $ "Productions: "
               ++ (show $ generationStateProductions state)
   -}
  return ()


debugLexers :: Generation ()
debugLexers = do
  GenerationState { generationStateMaybeCompiledLexers = Just lexers } <- get
  mapM_ (\(name, binaryFlag, anyLexer) -> do
          liftIO $ putStrLn $ "\nLexer " ++ name
                              ++ (if binaryFlag then " binary" else "")
          case anyLexer of
           Lexer lexer -> debugLexer lexer)
        lexers


debugLexer :: (Ord content, Bounded content, Enum content,
               Automaton a (EnumSet content) (Maybe (Maybe ClientExpression)) ())
           => a
           -> Generation ()
debugLexer automaton = do
  let toChar c = toEnum $ fromEnum c
      charToStr '\a' = "\\a"
      charToStr '\b' = "\\b"
      charToStr '\n' = "\\n"
      charToStr '\r' = "\\r"
      charToStr '\f' = "\\f"
      charToStr '\v' = "\\v"
      charToStr '\t' = "\\t"
      charToStr '\\' = "\\\\"
      charToStr c | (isPrint c) && (not $ isSpace c) = [c]
                  | ord c <= 0xFF = "\\x" ++ (padToLength 2 $ showHex (ord c) "")
                  | ord c <= 0xFFFF = "\\u" ++ (padToLength 4 $ showHex (ord c) "")
                  | otherwise = "\\U" ++ (padToLength 8 $ showHex (ord c) "")
      padToLength n text = (take (n - length text) $ cycle "0") ++ text
  mapM_ (\state -> do
          let datum = case automatonStateData automaton state of
                        Nothing -> ""
                        Just Nothing -> " WHITESPACE"
                        Just (Just (ClientExpression string))
                            -> " {" ++ string ++ "}"
              start = automatonStateStarting automaton state
              accepting = automatonStateAccepting automaton state
              transitionMap = automatonTransitionMap automaton state
          liftIO $ putStr $ if start then ">" else ""
          liftIO $ putStr $ if accepting then "*" else ""
          liftIO $ putStrLn $ (show state) ++ datum
          mapM_ (\input -> do
                   let resultStates
                           = fromJust $ Map.lookup input transitionMap
                   liftIO $ putStr "  "
                   mapM_ (\(start, end) -> do
                            if start == end
                              then liftIO $ putStr $ charToStr $ toChar start
                              else liftIO $ putStr
                                       $ (charToStr $ toChar start)
                                         ++ "-" ++ (charToStr $ toChar end))
                         $ EnumSet.toList input
                   liftIO $ putStr " ->"
                   mapM_ (\resultState -> do
                            liftIO $ putStr $ " " ++ (show resultState))
                         $ map fst resultStates
                   liftIO $ putStrLn "")
                $ Map.keys transitionMap)
        $ automatonStates automaton


debugIntermediateAutomaton
  :: (Ord content, Bounded content, Enum content,
      Automaton a
                (EnumSet content)
                (Maybe (Int, Maybe ClientExpression))
                (Maybe UniqueID))
  => a
  -> Generation ()
debugIntermediateAutomaton automaton = do
  let toChar c = toEnum $ fromEnum c
      charToStr '\a' = "\\a"
      charToStr '\b' = "\\b"
      charToStr '\n' = "\\n"
      charToStr '\r' = "\\r"
      charToStr '\f' = "\\f"
      charToStr '\v' = "\\v"
      charToStr '\t' = "\\t"
      charToStr '\\' = "\\\\"
      charToStr c | (isPrint c) && (not $ isSpace c) = [c]
                  | ord c <= 0xFF = "\\x" ++ (padToLength 2 $ showHex (ord c) "")
                  | ord c <= 0xFFFF = "\\u" ++ (padToLength 4 $ showHex (ord c) "")
                  | otherwise = "\\U" ++ (padToLength 8 $ showHex (ord c) "")
      padToLength n text = (take (n - length text) $ cycle "0") ++ text
  mapM_ (\state -> do
          let datum
                = case automatonStateData automaton state of
                    Nothing -> ""
                    Just (priority, Nothing)
                      -> (" " ++ show priority ++ " WHITESPACE")
                    Just (priority, Just (ClientExpression string))
                      -> (" " ++ show priority ++ " {" ++ string ++ "}")
              start = automatonStateStarting automaton state
              accepting = automatonStateAccepting automaton state
              transitionMap = automatonTransitionMap automaton state
          liftIO $ putStr $ if start then ">" else ""
          liftIO $ putStr $ if accepting then "*" else ""
          liftIO $ putStrLn $ (show state) ++ datum
          mapM_ (\input -> do
                   let resultStates
                           = fromJust $ Map.lookup input transitionMap
                   liftIO $ putStr "  "
                   mapM_ (\(start, end) -> do
                            if start == end
                              then liftIO $ putStr $ charToStr $ toChar start
                              else liftIO $ putStr
                                       $ (charToStr $ toChar start)
                                         ++ "-" ++ (charToStr $ toChar end))
                         $ EnumSet.toList input
                   liftIO $ putStr " ---"
                   mapM_ (\maybeTransitionPriority -> do
                            case maybeTransitionPriority of
                              Nothing -> return ()
                              Just transitionPriority -> do
                                liftIO $ putStr $ "("
                                                  ++ show transitionPriority
                                                  ++ ")")
                         $ map snd resultStates
                   liftIO $ putStr "--->"
                   mapM_ (\resultState -> do
                            liftIO $ putStr $ " " ++ (show resultState))
                         $ map fst resultStates
                   liftIO $ putStrLn "")
                $ Map.keys transitionMap)
        $ automatonStates automaton


debugParseTable :: Generation ()
debugParseTable = do
  GenerationState {
      generationStateMaybeParseTable = Just parseTable,
      generationStateMaybeParseTableStateDebugInfo = Just stateDebugInfo,
      generationStateMaybeParseTableProductionDebugInfo
        = Just productionDebugInfo
    } <- get
  liftIO $ putStrLn $ "PARSE TABLE"
  let conflicts =
        filter (\(_, _, actionList) -> length actionList > 1)
               $ concat
                 $ map (\(stateID, actionMap) ->
                          map (\(symbol, actionList) ->
                                 (stateID, symbol, actionList))
                              $ Map.toList actionMap)
                       $ Map.toList
                         $ case parseTable of
                             ParseTable _ transitionMap -> transitionMap
  if not $ null conflicts
    then do
      liftIO $ putStrLn ""
      liftIO $ putStrLn $ (show $ length conflicts) ++ " conflicts:"
      mapM_ (\(stateID, symbol, actionList) -> do
               liftIO $ putStrLn $ "State " ++ show stateID ++ " on "
                                   ++ show symbol ++ " => "
                                   ++ (intercalate ", "
                                                   $ map show actionList))
            conflicts
    else return ()
  liftIO $ putStrLn ""
  mapM_ (\(productionID, production) -> do
           liftIO $ putStrLn $ "Production " ++ (show productionID) ++ ": "
                               ++ (show production))
        $ Map.toList productionDebugInfo
  liftIO $ putStrLn ""
  mapM_ (\(symbol, stateID) -> do
           liftIO $ putStrLn $ "Start state for parsing " ++ (show symbol)
                               ++ " is " ++ (show stateID) ++ ".")
        $ Map.toList $ case parseTable of
                         ParseTable startStateMap _ -> startStateMap
  mapM_ (\(stateID, actionMap) -> do
           liftIO $ putStrLn ""
           liftIO $ putStrLn $ "State " ++ (show stateID) ++ ":"
           mapM_ (\item -> do
                    liftIO $ putStrLn $ "  " ++ (show item))
                 $ Set.elems $ fromJust $ Map.lookup stateID stateDebugInfo
           liftIO $ putStrLn $ "  "
           mapM_ (\(symbol, actionList) -> do
                    liftIO $ putStrLn $ "  "
                                        ++ (show symbol)
                                        ++ " => "
                                        ++ (intercalate ", "
                                                        $ map show actionList))
                 $ Map.toList actionMap)
        $ Map.toList $ case parseTable of
                         ParseTable _ transitionMap -> transitionMap


generate :: Generation ()
generate = do
  readSpecification
  -- debugSpecification
  processDeclarations
  -- debugEarlyGenerationState
  compileLexers
  -- debugLexers
  compileParsers
  debugParseTable
  writeOutput


readSpecification :: Generation ()
readSpecification = do
  GenerationState { generationStateInputFilename = inputFilename } <- get
  eitherErrorSpecification <- liftIO $ readSpecificationFile inputFilename
  case eitherErrorSpecification of
    Left error -> fail $ show error
    Right specification -> do
      state <- get
      put $ state { generationStateMaybeSpecification = Just specification }


processDeclarations :: Generation ()
processDeclarations = do
  processMonadDeclaration
  processErrorDeclaration
  processLexerDeclarations
  bootstrapProcessNonterminalDeclarations
  processTokensDeclaration
  processNonterminalDeclarations


processMonadDeclaration :: Generation ()
processMonadDeclaration = do
  state <- get
  let declarations = filter (\declaration -> case declaration of
                                MonadDeclaration _ _ -> True
                                _ -> False)
                            $ specificationDeclarations
                            $ fromJust
                            $ generationStateMaybeSpecification state
  case declarations of
    [] -> return ()
    [MonadDeclaration _ clientType]
        -> put $ state { generationStateMaybeMonadType = Just clientType }
    _ -> fail $ "Multiple MONAD declarations, at lines "
                ++ (englishList $ map (show . location) declarations)


processErrorDeclaration :: Generation ()
processErrorDeclaration = do
  state <- get
  let declarations = filter (\declaration -> case declaration of
                                ErrorDeclaration _ _ -> True
                                _ -> False)
                            $ specificationDeclarations
                            $ fromJust
                            $ generationStateMaybeSpecification state
  case declarations of
    [] -> return ()
    [ErrorDeclaration _ clientExpression]
        -> put $ state { generationStateMaybeErrorFunction = Just clientExpression }
    _ -> fail $ "Multiple ERROR declarations, at lines "
                ++ (englishList $ map (show . location) declarations)


processLexerDeclarations :: Generation ()
processLexerDeclarations = do
  state <- get
  let declarations = filter (\declaration -> case declaration of
                               UserLexerDeclaration _ _ _ _ -> True
                               LexerDeclaration _ _ _ _ _ _ -> True
                               _ -> False)
                            $ specificationDeclarations
                            $ fromJust
                            $ generationStateMaybeSpecification state
      initialDeclarations = filter (\declaration -> case declaration of
                                     UserLexerDeclaration _ True _ _ -> True
                                     LexerDeclaration _ True _ _ _ _ -> True
                                     _ -> False)
                                   $ specificationDeclarations
                                   $ fromJust
                                   $ generationStateMaybeSpecification state
  case declarations of
    [] -> fail $ "No LEXER or USER LEXER declarations."
    [declaration] -> return ()
    _ -> do
           let declarationsMissingNames
                   = filter (\declaration -> case declaration of
                                               LexerDeclaration _ _ _ Nothing _ _ -> True
                                               _ -> False)
                            declarations
           case declarationsMissingNames of
             [] -> return ()
             [declaration]
                 -> fail $ "Multiple LEXER declarations but missing NAME for the one at "
                           ++ "line " ++ (show $ location declaration)
             _ -> fail $ "Multiple LEXER declarations but missing NAMEs for the ones at "
                         ++ "lines " ++ (englishList $ map (show.location)
                                                           declarationsMissingNames)
  initialDeclaration <- case initialDeclarations of
    [] -> return $ head declarations
    [declaration] -> return declaration
    _ -> fail $ "Multiple INITIAL LEXER declarations, at lines "
                ++ (englishList $ map (show . location) initialDeclarations)
  let defaultLexerName = "joy_lexer"
      initialName = case initialDeclaration of
        UserLexerDeclaration _ _ _ maybeName -> maybe defaultLexerName id maybeName
        LexerDeclaration _ _ _ maybeName _ _ -> maybe defaultLexerName id maybeName
      namesAndLines = map (\declaration -> case declaration of
                            UserLexerDeclaration lineNumber _ _ maybeName
                              -> (maybe defaultLexerName id maybeName, lineNumber)
                            LexerDeclaration lineNumber _ _ maybeName _ _
                              -> (maybe defaultLexerName id maybeName, lineNumber))
                          declarations
      nonuniqueNames = map fst
                       $ deleteFirstsBy ((==) `on` fst)
                                        namesAndLines
                                        $ nubBy ((==) `on` fst) namesAndLines
      nonuniqueLines = map snd
                       $ filter (\(name, _) -> elem name nonuniqueNames)
                                namesAndLines
      invalidNameLines = map snd
                         $ filter (\(name, line) -> isUpper $ head name)
                                  namesAndLines
  case length invalidNameLines of
    0 -> return ()
    1 -> fail $ "Lexer with invalid name, at line " ++ (show $ head invalidNameLines)
    _ -> fail $ "Lexers with invalid names, at lines "
                ++ (englishList $ map show invalidNameLines)
  if length nonuniqueLines > 0
    then fail $ "Lexers with duplicate names, at lines "
                ++ (englishList $ map show nonuniqueLines)
                ++ "."
    else return ()
  let userDeclarations = filter (\declaration -> case declaration of
                                  UserLexerDeclaration _ _ _ _ -> True
                                  _ -> False)
                                declarations
      nonuserDeclarations = filter (\declaration -> case declaration of
                                     LexerDeclaration _ _ _ _ _ _ -> True
                                     _ -> False)
                                   declarations
      userNames = map (\(UserLexerDeclaration _ _ _ maybeName) ->
                        maybe defaultLexerName id maybeName)
                      userDeclarations
      nameDefinitionMap
          = Map.fromList
            $ map (\(LexerDeclaration _ _ binaryFlag maybeName maybeParent definition)
                       -> (maybe defaultLexerName id maybeName,
                           (definition, binaryFlag, maybeParent)))
                  nonuserDeclarations
      visitParent visited parentName = do
        if elem parentName visited
          then fail $ "Cycle in lexer parents: " ++ (englishList visited)
          else return ()
        let maybeParentDefinition = Map.lookup parentName nameDefinitionMap
        case maybeParentDefinition of
          Nothing -> if elem parentName userNames
                       then fail $ "Lexer " ++ parentName
                                   ++ " referenced as a parent but defined as USER."
                       else fail $ "Lexer " ++ parentName
                                   ++ " referenced as a parent but not defined."
          Just (parentDefinition, _, maybeGrandparent) -> do
            case maybeGrandparent of
              Nothing -> return parentDefinition
              Just grandparentName -> do
                recursiveResult <- visitParent (visited ++ [parentName]) grandparentName
                return $ parentDefinition ++ recursiveResult
      definitionIncludingParents baseName = do
        let (definition, binaryFlag, maybeParent)
                = fromJust $ Map.lookup baseName nameDefinitionMap
        case maybeParent of
          Nothing -> return (baseName, binaryFlag, definition)
          Just parentName -> do
            recursiveResult <- visitParent [baseName] parentName
            return (baseName, binaryFlag, definition ++ recursiveResult)
  nonuserNamesAndDefinitions <- mapM definitionIncludingParents
                                     $ Map.keys nameDefinitionMap
  let lexerInformation = LexerInformation {
                             lexerInformationInitialName = initialName,
                             lexerInformationUserNames = userNames,
                             lexerInformationNonuserNamesAndDefinitions
                                 = nonuserNamesAndDefinitions
                           }
  state <- get
  put $ state {
            generationStateMaybeLexerInformation = Just lexerInformation
          }


bootstrapProcessNonterminalDeclarations :: Generation ()
bootstrapProcessNonterminalDeclarations = do
  state <- get
  let declarations = filter (\declaration -> case declaration of
                                               NonterminalDeclaration { } -> True
                                               _ -> False)
                            $ specificationDeclarations
                            $ fromJust
                            $ generationStateMaybeSpecification state
      haveParsers = foldl (\haveParsers declaration ->
                            case nonterminalDeclarationParsers declaration of
                              [] -> haveParsers
                              _ -> True)
                          False
                          declarations
  state <- get
  put $ state { generationStateMaybeAnyParsersSpecified = Just haveParsers }
  return ()


processTokensDeclaration :: Generation ()
processTokensDeclaration = do
  state <- get
  let declarations = filter (\declaration -> case declaration of
                                TokensDeclaration _ _ _ -> True
                                _ -> False)
                            $ specificationDeclarations
                            $ fromJust
                            $ generationStateMaybeSpecification state
  case declarations of
    [] -> fail $ "Missing TOKENS declaration."
    [TokensDeclaration _ clientType definitions]
        -> do
             let terminals = map fst definitions
                 terminalPatternMap = Map.fromList definitions
                 patternTerminalAlist
                   = map (\(terminal, pattern) -> (pattern, terminal))
                         definitions
             put $ state {
                      generationStateMaybeTokenType = Just clientType,
                      generationStateMaybeTerminals = Just terminals,
                      generationStateMaybeTerminalPatternMap
                        = Just terminalPatternMap,
                      generationStateMaybePatternTerminalAlist
                        = Just patternTerminalAlist
                    }
    _ -> fail $ "Multiple TOKENS declarations, at lines "
                ++ (englishList $ map (show . location) declarations)


processNonterminalDeclarations :: Generation ()
processNonterminalDeclarations = do
  state <- get
  let declarations = filter (\declaration -> case declaration of
                                               NonterminalDeclaration { } -> True
                                               _ -> False)
                            $ specificationDeclarations
                            $ fromJust
                            $ generationStateMaybeSpecification state
      nonterminals
        = map (\declaration -> nonterminalDeclarationGrammarSymbol declaration)
              declarations
      nonterminalTypeMap
        = Map.fromList
          $ map (\declaration ->
                   (nonterminalDeclarationGrammarSymbol declaration,
                    nonterminalDeclarationType declaration))
                declarations
      productions
        = concat
          $ map (\declaration ->
                   let leftHandSide
                         = nonterminalDeclarationGrammarSymbol declaration
                       rightHandSidesAndClientActions
                         = nonterminalDeclarationRightHandSides declaration
                   in map (\(rightHandSide, clientAction)
                             -> Production leftHandSide
                                           rightHandSide
                                           clientAction)
                          rightHandSidesAndClientActions)
                declarations
      parserInformationMap
        = Map.fromList
          $ concat
          $ map (\declaration ->
                   let leftHandSide
                         = nonterminalDeclarationGrammarSymbol declaration
                       parsers
                         = nonterminalDeclarationParsers declaration
                   in map (\(partial, clientIdentifier)
                             -> (leftHandSide,
                                 ParserInformation {
                                   parserInformationGrammarSymbol
                                     = leftHandSide,
                                   parserInformationPartial = partial,
                                   parserInformationClientIdentifier
                                     = clientIdentifier
                                 }))
                          parsers)
                declarations
  put $ state {
          generationStateMaybeNonterminals = Just nonterminals,
          generationStateMaybeNonterminalTypeMap = Just nonterminalTypeMap,
          generationStateMaybeProductions = Just productions,
          generationStateMaybeParserInformationMap = Just parserInformationMap
        }
  return ()


compileLexers :: Generation ()
compileLexers = do
  GenerationState { generationStateMaybeLexerInformation = maybeInformation } <- get
  let names = map (\(a, _, _) -> a)
                  $ lexerInformationNonuserNamesAndDefinitions
                  $ fromJust maybeInformation
      binaryFlags = map (\(_, a, _) -> a)
                    $ lexerInformationNonuserNamesAndDefinitions
                    $ fromJust maybeInformation
      definitions = map (\(_, _, a) -> a)
                    $ lexerInformationNonuserNamesAndDefinitions
                    $ fromJust maybeInformation
  compiledLexers <- mapM (\(definition, binaryFlag) -> do
                           let normalItems
                                 = map (\item ->
                                          case item of
                                            (LexerNormalItem a b c) -> (a, b, Just c)
                                            (LexerWhitespaceItem a b) -> (a, b, Nothing))
                                       $ filter (\item ->
                                                   case item of
                                                     LexerNormalItem _ _ _ -> True
                                                     LexerWhitespaceItem _ _ -> True
                                                     _ -> False)
                                                definition
                               subexpressionItems
                                   = map (\(LexerSubexpressionItem a b c d)
                                              -> (a, b, c, d))
                                           $ filter (\item -> case item of
                                                      LexerSubexpressionItem _ _ _ _
                                                          -> True
                                                      _ -> False)
                                                    definition
                           compileLexer normalItems subexpressionItems binaryFlag)
                         $ zip definitions binaryFlags
  state <- get
  put $ state { generationStateMaybeCompiledLexers = Just $ zip3 names
                                                                 binaryFlags
                                                                 compiledLexers }
  return ()


compileLexer :: [(LineNumber, String, Maybe ClientExpression)]
             -> [(LineNumber, String, String, Maybe ClientExpression)]
             -> Bool
             -> Generation AnyLexer
compileLexer regexpStringResultTuples subexpressionTuples binaryFlag = do
  let attempt function lineNumber = do
        let eitherErrorResult = function
        case eitherErrorResult of
          Left message -> fail $ message ++ " at line " ++ (show lineNumber) ++ "."
          Right result -> return result
      
      compileLexer' :: (Ord content, Bounded content, Enum content)
                    => Generation (DFA (EnumSet content)
                                       (Maybe (Maybe ClientExpression))
                                       ())
      compileLexer' = do
        subexpressions
            <- mapM (\(lineNumber, _, regexpString, _)
                         -> attempt (parseRegexp regexpString binaryFlag)
                                    lineNumber)
                    subexpressionTuples
        let subexpressionBindingMap
                = Map.fromList $ zip (map (\(_, name, _, _) -> name)
                                          subexpressionTuples)
                                     $ zip subexpressions
                                           (map (\(_, _, _, maybeExpression)
                                                     -> Just maybeExpression)
                                                subexpressionTuples)
        regexps <- mapM (\(lineNumber, regexpString, _) -> do
                           regexp <- attempt (parseRegexp regexpString binaryFlag)
                                             lineNumber
                           attempt (substituteRegexpSubexpressions
                                     subexpressionBindingMap
                                     regexp)
                                   lineNumber)
                        regexpStringResultTuples
        nfa <- withUniquenessPurpose
          (\tagIDUniquenessPurpose ->
             withUniquenessPurpose
               (\leafPositionUniquenessPurpose ->
                  regexpsToNFA regexps
                               tagIDUniquenessPurpose
                               leafPositionUniquenessPurpose))
        -- debugIntermediateAutomaton nfa
        eitherMessageDFA <- nfaToDFA nfa
        case eitherMessageDFA of
          Left message -> fail message
          Right dfa -> return dfa
  case binaryFlag of
    False -> do
      dfa <- compileLexer'
      return $ Lexer (dfa :: Lexer Char)
    True -> do
      dfa <- compileLexer'
      return $ Lexer (dfa :: Lexer Word8)


compileParsers :: Generation ()
compileParsers = do
  state@GenerationState {
                   generationStateMaybeParserInformationMap
                     = Just parserInformationMap,
                   generationStateMaybeTerminals = Just terminals,
                   generationStateMaybeNonterminals = Just nonterminals,
                   generationStateMaybeProductions = Just productions
                 } <- get
  let startSymbols = Map.keys parserInformationMap
      (parseTable, stateDebugInfo, productionDebugInfo)
        = compileParseTable nonterminals terminals productions startSymbols
  put $ state {
          generationStateMaybeParseTable = Just parseTable,
          generationStateMaybeParseTableStateDebugInfo = Just stateDebugInfo,
          generationStateMaybeParseTableProductionDebugInfo
            = Just productionDebugInfo
        }


writeOutput :: Generation ()
writeOutput = do
  let writeOutput' file = do
                outputHeader file
                outputPrologue file
                outputSubheader file
                outputLexers file
                outputEpilogue file
  GenerationState { generationStateOutputFilename = outputFilename } <- get
  withFile outputFilename WriteMode writeOutput'
  return ()


outputHeader :: Handle -> Generation ()
outputHeader file = do
  timestamp <- liftIO $ getPOSIXTime
  GenerationState { generationStateInputFilename = inputFilename } <- get
  let formattedTimestamp = formatTime defaultTimeLocale
                                      "%Y-%m-%d %H:%M UTC"
                                      $ posixSecondsToUTCTime timestamp
      originalFilename = fromJust $ filePathFileComponent inputFilename
  liftIO $ hPutStrLn file $ "-- DO NOT EDIT this file; it was automatically generated."
  liftIO $ hPutStrLn file $ "-- Created by Joy 1.0 from "
                            ++ originalFilename
                            ++ " at "
                            ++ formattedTimestamp
                            ++ "."
  liftIO $ hPutStrLn file $ "{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses,"
  liftIO $ hPutStrLn file $ "             FunctionalDependencies #-}"


outputPrologue :: Handle -> Generation ()
outputPrologue file = do
  GenerationState { generationStateMaybeSpecification = Just specification } <- get
  outputClientRaw file $ specificationOutputHeader specification


outputEpilogue :: Handle -> Generation ()
outputEpilogue file = do
  GenerationState { generationStateMaybeSpecification = Just specification } <- get
  outputClientRaw file $ specificationOutputFooter specification


outputClientRaw :: Handle -> ClientRaw -> Generation ()
outputClientRaw file (ClientRaw lineNumber content) = do
  GenerationState { generationStateInputFilename = inputFilename } <- get
  liftIO $ hPutStr file $ "{-# LINE "
                          ++ (show $ lineNumber)
                          ++ " \""
                          ++ (fromJust $ filePathFileComponent inputFilename)
                          ++ "\" #-}\n"
                          ++ (content)
                          ++ "\n"


outputSubheader :: Handle -> Generation ()
outputSubheader file = do
  liftIO $ hPutStr file $ "{-# LINE 1 \"(Code generated by Joy)\" #-}\n"


outputLexers :: Handle -> Generation ()
outputLexers file = do
  GenerationState { generationStateMaybeCompiledLexers = Just lexers } <- get
  if length lexers == 0
    then return ()
    else do
      let out string = liftIO $ hPutStr file string
      out $ "class (Monad m, Enum content) => MonadLexer m content | m -> content where\n"
      out $ "  peekInput :: Int -> m (Maybe content)\n"
      out $ "  consumeInput :: Int -> m [content]\n"
      out $ "\n"
      out $ "\n"
  mapM_ (\(name, binaryFlag, anyLexer) -> outputLexer file name binaryFlag anyLexer)
        $ lexers


outputLexer :: Handle -> String -> Bool -> AnyLexer -> Generation ()
outputLexer file name binaryFlag anyLexer = do
  state <- get
  let out string = liftIO $ hPutStr file string
      maybeMonadType = generationStateMaybeMonadType state
      Just (ClientType tokenType) = generationStateMaybeTokenType state
  case maybeMonadType of
    Nothing -> do
      out $ name ++ " :: "
      out $ case binaryFlag of
              False -> "String"
              True -> "[Word8]"
      out $ " -> ["
      out $ trim tokenType
      out $ "]\n"
      out $ name ++ " input =\n"
    Just (ClientType monadType) -> do
      out $ name ++ " :: "
      out $ trim monadType
      out $ " (Maybe ("
      out $ trim tokenType
      out $ "))\n"
      out $ name ++ " = do\n"
      out $ "  let lex :: Int -> Int -> (Maybe (Int, Int))\n"
      out $ "          -> "
      out $ trim monadType
      out $ " (Maybe (Either String ("
      out $ trim tokenType
      out $ ")))\n"
      out $ "      lex offset state maybeBestMatch = do\n"
      out $ "        maybeC <- peekInput offset\n"
      out $ "        case maybeC of\n"
      out $ "          Nothing -> returnMatch maybeBestMatch\n"
      out $ "          Just c -> do\n"
      out $ "            let o = fromEnum c\n"
      out $ "                shift state = lex (offset+1) state maybeBestMatch\n"
      out $ "                shiftAndAccept state = lex (offset+1) state\n"
      out $ "                                           $ Just (offset+1, state)\n"
      out $ "                reject = returnMatch maybeBestMatch\n"
      out $ "            case state of\n"
      Lexer lexer <- return anyLexer
      let stateNumberIDMap = Map.fromList $ zip [0..] (automatonStates lexer)
          stateIDNumberMap = Map.fromList $ zip (automatonStates lexer) [0..]
          stateCount = Map.size stateNumberIDMap
          stateNumberWidth = numberWidth $ fromIntegral $ stateCount - 1
      mapM_ (\stateNumber -> do
               let stateID = fromJust $ Map.lookup stateNumber stateNumberIDMap
                   transitions
                       = concat
                         $ map (\(enumSet, [(targetID, _)]) ->
                                 let target = fromJust $ Map.lookup targetID
                                                                    stateIDNumberMap
                                 in map (\(rangeStart, rangeEnd) ->
                                          (rangeStart, rangeEnd, target))
                                        $ EnumSet.toList enumSet)
                               $ Map.toList $ automatonTransitionMap lexer stateID
               mapM_ (\((rangeStart, rangeEnd, target), first) -> do
                        let targetID = fromJust $ Map.lookup target stateNumberIDMap
                            maybeTargetData = automatonStateData lexer targetID
                        out $ "              "
                        if first
                          then out $ (rightPadToWidth stateNumberWidth ' '
                                                 $ show stateNumber)
                          else out $ (rightPadToWidth stateNumberWidth ' ' "")
                        out $ " | (o >= "
                        out $ show $ fromEnum rangeStart
                        out $ ") && (o <= "
                        out $ show $ fromEnum rangeEnd
                        out $ ") -> "
                        case maybeTargetData of
                          Nothing -> out $ "shift " ++ (show target)
                          Just _ -> out $ "shiftAndAccept " ++ (show target)
                        out $ "\n")
                     $ zip transitions $ [True] ++ cycle [False]
               out $ "              "
               if length transitions == 0
                 then out $ (rightPadToWidth stateNumberWidth ' ' $ show stateNumber)
                 else out $ (rightPadToWidth stateNumberWidth ' ' "")
               out $ " | otherwise -> reject\n")
            [0..stateCount-1]
      out $ "      returnMatch :: (Maybe (Int, Int))\n"
      out $ "                  -> "
      out $ trim monadType
      out $ " (Maybe (Either String ("
      out $ trim tokenType
      out $ ")))\n"
      out $ "      returnMatch Nothing = return Nothing\n"
      out $ "      returnMatch (Just (inputLength, state)) = do\n"
      out $ "        joy_0 <- consumeInput inputLength\n"
      out $ "        case state of\n"
      mapM_ (\state -> do
               let stateID = fromJust $ Map.lookup state stateNumberIDMap
                   maybeMaybeTokenConstructor = automatonStateData lexer stateID
               case maybeMaybeTokenConstructor of
                 Nothing -> return ()
                 Just maybeTokenConstructor -> do
                   out $ "          "
                   out $ (rightPadToWidth stateNumberWidth ' ' $ show state)
                   out $ " -> return $ Just $ "
                   case maybeTokenConstructor of
                     Nothing -> out $ "Left joy_0"
                     Just tokenConstructor -> do
                       out $ "Right $ "
                       out $ trim $ clientExpressionSubstitute $ tokenConstructor
                   out $ "\n")
            [0..stateCount-1]
      out $ "      lexPastWhitespace :: "
      out $ trim monadType
      out $ " (Maybe ("
      out $ trim tokenType
      out $ "))\n"
      out $ "      lexPastWhitespace = do\n"
      out $ "        prospectiveResult <- lex 0 0 Nothing\n"
      out $ "        case prospectiveResult of\n"
      out $ "          Nothing -> return Nothing\n"
      out $ "          Just (Left _) -> lexPastWhitespace\n"
      out $ "          Just (Right result) -> return $ Just result\n"
      out $ "  lexPastWhitespace\n"
  out $ "\n"
