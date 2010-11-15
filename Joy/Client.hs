module Joy.Client (
                   ClientRaw(..),
                   ClientType(..),
                   ClientPattern(..),
                   ClientIdentifier(..),
                   ClientExpression(..),
                   ClientAction(..),
                   clientExpressionSubstitute,
                   clientPatternSubstituteWildcards
                  )
    where


import Data.Char
import Data.List

import Joy.Documentation


data ClientRaw = ClientRaw LineNumber String


data ClientType = ClientType String


data ClientPattern = ClientPattern String


data ClientIdentifier = ClientIdentifier String


data ClientExpression = ClientExpression String


data ClientAction = ClientAction Bool String


clientExpressionSubstitute :: ClientExpression -> String
clientExpressionSubstitute (ClientExpression input) =
  let substitute "" = ""
      substitute ('$':rest) =
        let (firstWord, rest') = maybe ("", rest)
                                       (\point -> splitAt point rest)
                                       (elemIndex ' ' rest)
            maybeIndex = if (length firstWord > 0) && (all isDigit firstWord)
                           then Just $ (read firstWord :: Int)
                           else Nothing
        in case maybeIndex of
             Nothing -> "$" ++ firstWord ++ substitute rest'
             Just index -> "joy_" ++ (show index) ++ substitute rest'
      substitute (c:rest) = c : substitute rest
  in substitute input


clientPatternSubstituteWildcards :: ClientPattern -> String
clientPatternSubstituteWildcards (ClientPattern input) =
  let substitute "" = ""
      substitute ('$':'$':rest) = '_' : substitute rest
      substitute (c:rest) = c : substitute rest
  in substitute input
