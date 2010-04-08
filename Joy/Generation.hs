{-# LANGUAGE ExistentialQuantification, FlexibleContexts, FlexibleInstances,
             TypeSynonymInstances #-}
module Joy.Generation (
                       Generation(..),
                       GenerationError(..),
                       GenerationState(..),
                       LexerInformation(..),
                       Lexer(..),
                       AnyLexer(..),
                       mkGenerationState,
                       runGeneration,
                       suspendGeneration,
                       reenterGeneration,
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
import Data.Time
import Data.Time.Clock.POSIX
import Data.Word
import Numeric
import System.IO
import System.Locale

import Joy.Automata
import Joy.Client
import Joy.Documentation
import Joy.EnumSet (EnumSet)
import qualified Joy.EnumSet as EnumSet
import Joy.Uniqueness
import Joy.Regexp
import Joy.Specification


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
        generationStateMaybeNonterminals :: Maybe [GrammarSymbol],
        generationStateMaybeProductions
            :: Maybe [(GrammarSymbol, [GrammarSymbol], ClientExpression)]
      }


data LexerInformation = LexerInformation {
        lexerInformationInitialName :: String,
        lexerInformationUserNames :: [String],
        lexerInformationNonuserNamesAndDefinitions
            :: [(String, Bool, [LexerDefinitionItem])]
    }


type Lexer content = DFA (EnumSet content) (Maybe ClientExpression) ()

data AnyLexer = CharLexer (Lexer Char)
              | Word8Lexer (Lexer Word8)


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
        generationStateMaybeNonterminals = Nothing,
        generationStateMaybeProductions = Nothing
      }


runGeneration :: (Generation a) -> GenerationState -> IO (Either GenerationError a)
runGeneration action state = runUniqueT $ flip evalStateT state $ runErrorT action


suspendGeneration :: Generation (GenerationState, UniqueState)
suspendGeneration = do
  generationState <- get
  uniqueState <- getUniqueState
  return (generationState, uniqueState)


reenterGeneration :: (GenerationState, UniqueState)
                  -> (Generation a)
                  -> IO (Either GenerationError a)
reenterGeneration (generationState, uniqueState) action
    = reenterUniqueT uniqueState $ flip evalStateT generationState $ runErrorT action


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
  mapM_ (\(name, binaryFlag, lexer) -> do
          liftIO $ putStrLn $ "\nLexer " ++ name
                              ++ (if binaryFlag then " binary" else "")
          case lexer of
            CharLexer lexer -> debugAutomaton lexer
            Word8Lexer lexer -> debugAutomaton lexer)
        lexers


debugAutomaton :: (Ord content, Bounded content, Enum content,
                   Automaton a (EnumSet content) (Maybe ClientExpression) ())
               => a
               -> Generation ()
debugAutomaton automaton = do
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
                        Nothing -> "Nothing"
                        Just (ClientExpression string)
                            -> "Just {" ++ string ++ "}"
              start = automatonStateStarting automaton state
              accepting = automatonStateAccepting automaton state
              transitionMap = automatonTransitionMap automaton state
          liftIO $ putStr $ if start then ">" else ""
          liftIO $ putStr $ if accepting then "*" else ""
          liftIO $ putStrLn $ (show state) ++ " " ++ datum
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


generate :: Generation ()
generate = do
  readSpecification
  -- debugSpecification
  processDeclarations
  -- debugEarlyGenerationState
  compileLexers
  -- debugLexers
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
                               UserLexerDeclaration _ _ _ -> True
                               LexerDeclaration _ _ _ _ _ _ -> True
                               _ -> False)
                            $ specificationDeclarations
                            $ fromJust
                            $ generationStateMaybeSpecification state
      initialDeclarations = filter (\declaration -> case declaration of
                                     UserLexerDeclaration _ True _ -> True
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
        UserLexerDeclaration _ _ name -> name
        LexerDeclaration _ _ _ maybeName _ _ -> maybe defaultLexerName id maybeName
      namesAndLines = map (\declaration -> case declaration of
                            UserLexerDeclaration lineNumber _ name -> (name, lineNumber)
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
                                  UserLexerDeclaration _ _ _ -> True
                                  _ -> False)
                                declarations
      nonuserDeclarations = filter (\declaration -> case declaration of
                                     LexerDeclaration _ _ _ _ _ _ -> True
                                     _ -> False)
                                   declarations
      userNames = map (\(UserLexerDeclaration _ _ name) -> name) userDeclarations
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
             put $ state { generationStateMaybeTokenType = Just clientType }
    _ -> fail $ "Multiple TOKENS declarations, at lines "
                ++ (englishList $ map (show . location) declarations)


processNonterminalDeclarations :: Generation ()
processNonterminalDeclarations = do
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
                                   = map (\(LexerNormalItem a b c) -> (a, b, c))
                                         $ filter (\item -> case item of
                                                    LexerNormalItem _ _ _ -> True
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


compileLexer :: [(LineNumber, String, ClientExpression)]
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
                    => Generation (DFA (EnumSet content) (Maybe ClientExpression) ())
      compileLexer' = do
        regexps <- mapM (\(lineNumber, regexpString, _)
                             -> attempt (parseRegexp regexpString binaryFlag)
                                        lineNumber)
                        regexpStringResultTuples
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
                                                     -> maybeExpression)
                                                subexpressionTuples)
        nfas <- mapM (\(regexp, priority, result) -> regexpToNFA regexp
                                                                 subexpressionBindingMap
                                                                 (priority, result))
                     $ zip3 regexps
                            [0..]
                            (map (\(_, _, result) -> result)
                                 regexpStringResultTuples)
        let combinedNFA = combineNFAs nfas
        eitherMessageDFA <- nfaToDFA combinedNFA
        case eitherMessageDFA of
          Left message -> fail message
          Right dfa -> return dfa
  case binaryFlag of
    False -> do
      dfa <- compileLexer'
      return $ CharLexer dfa
    True -> do
      dfa <- compileLexer'
      return $ Word8Lexer dfa


writeOutput :: Generation ()
writeOutput = do
  let writeOutput' file = do
                outputHeader file
                outputPrologue file
                outputLexers file
                outputEpilogue file
  GenerationState { generationStateOutputFilename = outputFilename } <- get
  savedState <- suspendGeneration
  liftIO $ withFile outputFilename WriteMode
    (\file -> reenterGeneration savedState $ writeOutput' file)
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


outputPrologue :: Handle -> Generation ()
outputPrologue file = do
  GenerationState { generationStateMaybeSpecification = Just specification } <- get
  let ClientRaw prologue = specificationOutputHeader specification
  liftIO $ hPutStr file prologue


outputEpilogue :: Handle -> Generation ()
outputEpilogue file = do
  GenerationState { generationStateMaybeSpecification = Just specification } <- get
  let ClientRaw epilogue = specificationOutputFooter specification
  liftIO $ hPutStr file epilogue


outputLexers :: Handle -> Generation ()
outputLexers file = do
  GenerationState { generationStateMaybeCompiledLexers = lexers } <- get
  mapM_ (\(name, binaryFlag, anyLexer) -> outputLexer file name binaryFlag anyLexer)
        $ fromJust lexers


outputLexer :: Handle -> String -> Bool -> AnyLexer -> Generation ()
outputLexer file name binaryFlag anyLexer = do
  state <- get
  let maybeMonadType = generationStateMaybeMonadType state
      Just (ClientType tokenType) = generationStateMaybeTokenType state
  liftIO $ hPutStr file $ name ++ " :: "
  case maybeMonadType of
    Nothing -> do
      liftIO $ hPutStr file $ case binaryFlag of
                          False -> "String"
                          True -> "[Word8]"
      liftIO $ hPutStr file $ " -> ["
      liftIO $ hPutStr file $ trim tokenType
      liftIO $ hPutStr file $ "]\n"
      liftIO $ hPutStr file $ name ++ " input =\n"
    Just (ClientType monadType) -> do
      liftIO $ hPutStr file $ trim monadType
      liftIO $ hPutStr file $ " (Maybe ("
      liftIO $ hPutStr file $ trim tokenType
      liftIO $ hPutStr file $ "))\n"
      liftIO $ hPutStr file $ name ++ " = do\n"
  liftIO $ hPutStr file $ "\n"
  liftIO $ hPutStr file $ "\n"
