{-# LANGUAGE ExistentialQuantification, FlexibleContexts, FlexibleInstances,
             TypeSynonymInstances #-}
module Joy.Generation (
                       Generation(..),
                       GenerationError(..),
                       GenerationState(..),
                       LexerInformation(..),
                       Lexer(..),
                       AnyLexer(..),
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
import Data.Word
import Numeric

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
        generationStateSpecification :: Specification,
        generationStateMaybeMonadType :: Maybe ClientType,
        generationStateMaybeLexerInformation :: Maybe LexerInformation,
        generationStateMaybeErrorFunction :: Maybe ClientExpression,
        generationStateCompiledLexers :: [(String, Bool, AnyLexer)],
        generationStateTerminals :: [GrammarSymbol],
        generationStateNonterminals :: [GrammarSymbol],
        generationStateProductions
            :: [(GrammarSymbol, [GrammarSymbol], ClientExpression)]
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
  GenerationState { generationStateCompiledLexers = lexers } <- get
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
  -- debugSpecification
  processDeclarations
  -- debugEarlyGenerationState
  compileLexers
  debugLexers


processDeclarations :: Generation ()
processDeclarations = do
  processMonadDeclaration
  processErrorDeclaration
  processLexerDeclarations
  processTokensDeclaration
  processNonterminalDeclarations


processMonadDeclaration :: Generation ()
processMonadDeclaration = do
  state <- get
  let declarations = filter (\declaration -> case declaration of
                                MonadDeclaration _ _ -> True
                                _ -> False)
                            $ specificationDeclarations
                            $ generationStateSpecification state
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
                            $ generationStateSpecification state
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
                            $ generationStateSpecification state
      initialDeclarations = filter (\declaration -> case declaration of
                                     UserLexerDeclaration _ True _ -> True
                                     LexerDeclaration _ True _ _ _ _ -> True
                                     _ -> False)
                                   $ specificationDeclarations
                                   $ generationStateSpecification state
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


processTokensDeclaration :: Generation ()
processTokensDeclaration = do
  return ()


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
  put $ state { generationStateCompiledLexers = zip3 names binaryFlags compiledLexers }
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
