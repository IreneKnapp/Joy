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
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Word

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
        generationStateCompiledLexers :: [(ClientExpression, Bool, AnyLexer)],
        generationStateTerminals :: [GrammarSymbol],
        generationStateNonterminals :: [GrammarSymbol],
        generationStateProductions
            :: [(GrammarSymbol, [GrammarSymbol], ClientExpression)]
      }


data LexerInformation = LexerInformation {
        lexerInformationMaybeInitialName :: Maybe ClientExpression,
        lexerInformationUserNames :: [ClientExpression],
        lexerInformationNonuserNamesAndDefinitions
            :: [(ClientExpression, Bool, [(LineNumber, String, ClientExpression)])]
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
  mapM_ (\(ClientExpression name, binaryFlag, lexer) -> do
          liftIO $ putStrLn $ "\nLexer {" ++ name ++ "}"
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
                              then liftIO $ putStr $ [toChar start]
                              else liftIO $ putStr
                                       $ [toChar start] ++ "-" ++ [toChar end])
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
                               LexerDeclaration _ _ _ _ _ -> True
                               _ -> False)
                            $ specificationDeclarations
                            $ generationStateSpecification state
      initialDeclarations = filter (\declaration -> case declaration of
                                     UserLexerDeclaration _ True _ -> True
                                     LexerDeclaration _ True _ _ _ -> True
                                     _ -> False)
                                   $ specificationDeclarations
                                   $ generationStateSpecification state
  case declarations of
    [] -> fail $ "No LEXER or USER LEXER declarations."
    [declaration] -> return ()
    _ -> do
           let declarationsMissingNames
                   = filter (\declaration -> case declaration of
                                               LexerDeclaration _ _ _ Nothing _ -> True
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
  let maybeInitialName = case initialDeclaration of
        UserLexerDeclaration _ _ name -> Just name
        LexerDeclaration _ _ _ maybeName _ -> maybeName
      userDeclarations = filter (\declaration -> case declaration of
                                  UserLexerDeclaration _ _ _ -> True
                                  _ -> False)
                                declarations
      nonuserDeclarations = filter (\declaration -> case declaration of
                                     LexerDeclaration _ _ _ _ _ -> True
                                     _ -> False)
                                   declarations
      userNames = map (\(UserLexerDeclaration _ _ name) -> name) userDeclarations
      nonuserNamesAndDefinitions
          = map (\(LexerDeclaration _ _ binary maybeName definition)
                     -> let name = maybe (ClientExpression "_Joy_lexer")
                                         id
                                         maybeName
                        in (name, binary, definition))
                nonuserDeclarations
      lexerInformation = LexerInformation {
                             lexerInformationMaybeInitialName = maybeInitialName,
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
  compiledLexers <- mapM (uncurry compileLexer)
                         $ zip definitions binaryFlags
  state <- get
  put $ state { generationStateCompiledLexers = zip3 names binaryFlags compiledLexers }
  return ()


compileLexer :: [(LineNumber, String, ClientExpression)]
             -> Bool
             -> Generation AnyLexer
compileLexer regexpStringResultTuples binaryFlag = do
  case binaryFlag of
    False -> do
      regexps <- mapM (\(lineNumber, regexpString, _) -> do
                         let eitherErrorRegexp = parseRegexp regexpString
                         case eitherErrorRegexp of
                           Left message -> fail $ message
                                                  ++ " at line "
                                                  ++ (show lineNumber)
                                                  ++ "."
                           Right regexp -> return regexp)
                      regexpStringResultTuples
      nfas <- mapM (\(regexp, result) -> regexpToNFA regexp result)
                   $ zip regexps (map (\(_, _, result) -> result)
                                      regexpStringResultTuples)
      let combinedNFA = combineNFAs nfas
      eitherMessageDFA <- nfaToDFA combinedNFA
      case eitherMessageDFA of
        Left message -> fail message
        Right dfa -> return $ CharLexer dfa
    True -> do
      regexps <- mapM (\(lineNumber, regexpString, _) -> do
                         let eitherErrorRegexp = parseRegexp regexpString
                         case eitherErrorRegexp of
                           Left message -> fail $ message
                                                  ++ " at line "
                                                  ++ (show lineNumber)
                                                  ++ "."
                           Right regexp -> return regexp)
                      regexpStringResultTuples
      nfas <- mapM (\(regexp, result) -> regexpToNFA regexp result)
                   $ zip regexps (map (\(_, _, result) -> result)
                                      regexpStringResultTuples)
      let combinedNFA = combineNFAs nfas
      eitherMessageDFA <- nfaToDFA combinedNFA
      case eitherMessageDFA of
        Left message -> fail message
        Right dfa -> return $ Word8Lexer dfa
