module Main (main)
    where

import Control.Monad.Error
import Control.Monad.State
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import System.Environment
import System.Exit
import System.IO

import Joy.Automata
import Joy.EnumSets as EnumSets
import Joy.Regexps
import Joy.Specification
import Joy.Types


mkGenerationState :: Specification -> GenerationState
mkGenerationState specification
    = GenerationState {
        generationStateSpecification = specification,
        generationStateMaybeMonadType = Nothing,
        generationStateMaybeLexerInformation = Nothing,
        generationStateMaybeErrorFunction = Nothing,
        generationStateCompiledLexers = [],
        generationStateTerminals = [],
        generationStateNonterminals = [],
        generationStateProductions = []
      }


main :: IO ()
main = do
  arguments <- getArgs
  inputFilename <- case arguments of
    [inputFilename] -> return inputFilename
    _ -> usage
  eitherErrorSpecification <- readSpecificationFile inputFilename
  case eitherErrorSpecification of
    Left error -> putStrLn $ show error
    Right specification -> do
      let state = mkGenerationState specification
      (state, result) <- runUniqueT $ evalStateT (do
                                                   result <- runErrorT generate
                                                   state <- get
                                                   return (state, result))
                                                 state
      case result of
        Left error -> putStrLn $ show error
        Right () -> return ()


usage :: IO a
usage = do
  name <- getProgName
  putStrLn $ "Usage: " ++ name ++ " input.joy"
  exitFailure


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


generate :: Generation ()
generate = do
  -- debugSpecification
  processDeclarations
  -- debugEarlyGenerationState
  compileLexers
  -- debugLexers


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
                               LexerDeclaration _ _ _ _ -> True
                               _ -> False)
                            $ specificationDeclarations
                            $ generationStateSpecification state
      initialDeclarations = filter (\declaration -> case declaration of
                                     UserLexerDeclaration _ True _ -> True
                                     LexerDeclaration _ True _ _ -> True
                                     _ -> False)
                                   $ specificationDeclarations
                                   $ generationStateSpecification state
  case declarations of
    [] -> fail $ "No LEXER or USER LEXER declarations."
    [declaration] -> return ()
    _ -> do
           let declarationsMissingNames
                   = filter (\declaration -> case declaration of
                                               LexerDeclaration _ _ Nothing _ -> True
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
        LexerDeclaration _ _ maybeName _ -> maybeName
      userDeclarations = filter (\declaration -> case declaration of
                                  UserLexerDeclaration _ _ _ -> True
                                  _ -> False)
                                declarations
      nonuserDeclarations = filter (\declaration -> case declaration of
                                     LexerDeclaration _ _ _ _ -> True
                                     _ -> False)
                                   declarations
      userNames = map (\(UserLexerDeclaration _ _ name) -> name) userDeclarations
      nonuserNamesAndDefinitions = map (\(LexerDeclaration _ _ maybeName definition)
                                        -> case maybeName of
                                             Nothing -> (ClientExpression "_Joy_lexer",
                                                         definition)
                                             Just name -> (name, definition))
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
  compiledLexers <- mapM compileLexer
                         $ map snd
                         $ lexerInformationNonuserNamesAndDefinitions
                         $ fromJust maybeInformation
  {-
  state <- get
  put $ state { generationStateCompiledLexers = compiledLexers }
  -}
  return ()


compileLexer :: [(LineNumber, String, ClientExpression)] -> Generation ()
compileLexer regexpStringResultTuples = do
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
               $ zip regexps (map (\(_, _, result) -> result) regexpStringResultTuples)
  let combinedNFA = combineNFAs nfas
  eitherMessageDFA <- nfaToDFA combinedNFA
  dfa <- case eitherMessageDFA of
           Left message -> fail message
           Right dfa -> return dfa
  liftIO $ let showAutomaton automaton = do
               mapM_ (\state -> do
                       let datum = case automatonStateData automaton state of
                                     Nothing -> "Nothing"
                                     Just (ClientExpression string)
                                         -> "Just {" ++ string ++ "}"
                           start = automatonStateStarting automaton state
                           accepting = automatonStateAccepting automaton state
                           transitionMap = automatonTransitionMap automaton state
                       putStr $ if start then ">" else ""
                       putStr $ if accepting then "*" else ""
                       putStrLn $ (show state) ++ " " ++ datum
                       mapM_ (\input -> do
                                let resultStates
                                        = fromJust $ Map.lookup input transitionMap
                                putStr "  "
                                mapM_ (\(start, end) -> do
                                         if start == end
                                           then putStr $ [start]
                                           else putStr $ [start] ++ "-" ++ [end])
                                      $ EnumSets.toList input
                                putStr " ->"
                                mapM_ (\resultState -> do
                                         putStr $ " " ++ (show resultState))
                                      $ map fst resultStates
                                putStrLn "")
                             $ Map.keys transitionMap)
                     $ automatonStates automaton
           in do
             mapM_ (\(nfa, regexpString) -> do
                      putStrLn ""
                      putStrLn $ (show regexpString)
                      showAutomaton nfa)
                    $ zip nfas $ map (\(_, a, _) -> a) regexpStringResultTuples
             putStrLn ""
             putStrLn "Combined NFA"
             showAutomaton combinedNFA
             putStrLn ""
             putStrLn "DFA"
             showAutomaton dfa
  return ()


englishList :: [String] -> String
englishList [] = ""
englishList [item] = item
englishList (a:b:[]) = a ++ " and " ++ b
englishList items = (intercalate ", " $ reverse $ drop 1 $ reverse items)
                    ++ ", and "
                    ++ (head $ reverse items)
