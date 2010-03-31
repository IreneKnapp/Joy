module Main (main)
    where

import Control.Monad.Error
import Control.Monad.State
import System.IO

import Joy.Types
import Joy.Specification


mkGenerationState :: Specification -> GenerationState
mkGenerationState specification
    = GenerationState {
        generationStateSpecification = specification,
        generationStateUserLexer = False,
        generationStateMaybeMonadType = Nothing,
        generationStateMaybeLexerName = Nothing,
        generationStateMaybeErrorFunction = Nothing,
        generationStateTerminals = [],
        generationStateNonterminals = [],
        generationStateProductions = []
      }


main :: IO ()
main = do
  eitherErrorSpecification <- readSpecificationFile "test.joy"
  case eitherErrorSpecification of
    Left error -> putStrLn $ show error
    Right specification -> do
      let state = mkGenerationState specification
      state <- execStateT (runErrorT generate) state
      putStrLn $ show state


debugSpecification :: Generation ()
debugSpecification = do
  let visitDeclaration (declaration:rest) = do
        liftIO $ putStrLn $ show declaration
        visitDeclaration rest
      visitDeclaration [] = return ()
  GenerationState { generationStateSpecification = specification } <- get
  visitDeclaration $ specificationDeclarations specification


generate :: Generation ()
generate = do
  -- debugSpecification
  processDeclarations


processDeclarations :: Generation ()
processDeclarations = do
  processMonadDeclaration
  processErrorDeclaration
  processLexerDeclaration
  processTokensDeclaration
  processNonterminalDeclarations


processMonadDeclaration :: Generation ()
processMonadDeclaration = do
  return ()


processErrorDeclaration :: Generation ()
processErrorDeclaration = do
  return ()


processLexerDeclaration :: Generation ()
processLexerDeclaration = do
  return ()


processTokensDeclaration :: Generation ()
processTokensDeclaration = do
  return ()


processNonterminalDeclarations :: Generation ()
processNonterminalDeclarations = do
  return ()
