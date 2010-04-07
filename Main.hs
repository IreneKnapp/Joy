{-# LANGUAGE FlexibleContexts #-}
module Main (main)
    where

import Control.Monad.Error
import Control.Monad.State
import Data.Set (Set)
import qualified Data.Set as Set
import System.Environment
import System.Exit
import System.IO

import Joy.Automata
import Joy.EnumSet as EnumSet
import Joy.Generation
import Joy.Specification
import Joy.Uniqueness


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
