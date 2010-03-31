module Main (main)
    where

import Control.Monad.Error
import Control.Monad.State
import System.IO

import Joy.Types
import Joy.Specification


main :: IO ()
main = do
  eitherErrorSpecification <- readSpecificationFile "test.joy"
  putStrLn $ show eitherErrorSpecification
