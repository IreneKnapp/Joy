module Main (main)
    where

import Control.Monad.Error
import Control.Monad.State
import Data.List
import System.Environment
import System.Exit
import System.IO

import Joy.Types
import Joy.Specification


mkGenerationState :: Specification -> GenerationState
mkGenerationState specification
    = GenerationState {
        generationStateUniqueIDCounter = 1,
        generationStateSpecification = specification,
        generationStateMaybeMonadType = Nothing,
        generationStateMaybeLexerInformation = Nothing,
        generationStateMaybeErrorFunction = Nothing,
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
      (state, result) <- evalStateT (do
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
  let visitDeclaration (declaration:rest) = do
        liftIO $ putStrLn $ show declaration
        visitDeclaration rest
      visitDeclaration [] = return ()
  GenerationState { generationStateSpecification = specification } <- get
  visitDeclaration $ specificationDeclarations specification


debugEarlyGenerationState :: Generation ()
debugEarlyGenerationState = do
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


englishList :: [String] -> String
englishList [] = ""
englishList [item] = item
englishList (a:b:[]) = a ++ " and " ++ b
englishList items = (intercalate ", " $ reverse $ drop 1 $ reverse items)
                    ++ ", and "
                    ++ (head $ reverse items)


getUniqueID :: Generation UniqueID
getUniqueID = do
  state@(GenerationState { generationStateUniqueIDCounter = uniqueID }) <- get
  put $ state { generationStateUniqueIDCounter = uniqueID + 1 }
  return uniqueID
