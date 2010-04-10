{-# LANGUAGE FlexibleContexts #-}
module Main (main)
    where

import Control.Monad.Error
import Control.Monad.State
import System.Environment
import System.Exit
import System.IO

import Joy.Generation
import Joy.Uniqueness


main :: IO ()
main = do
  arguments <- getArgs
  (inputFilename, outputFilename) <- case arguments of
    [inputFilename, outputFilename] -> return (inputFilename, outputFilename)
    _ -> usage
  let state = mkGenerationState inputFilename outputFilename
  result <- runUniqueT $ evalStateT (runErrorT generate) state
  case result of
    Left error -> do
      putStrLn $ show error
      exitFailure
    Right () -> return ()


usage :: IO a
usage = do
  name <- getProgName
  putStrLn $ "Usage: " ++ name ++ " input.joy output.hs"
  exitFailure
