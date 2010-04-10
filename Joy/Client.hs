module Joy.Client (
                   ClientRaw(..),
                   ClientType(..),
                   ClientExpression(..),
                   ClientAction(..),
                   clientExpressionSubstitute
                  )
    where


import Data.Char
import Data.List


data ClientRaw = ClientRaw String


data ClientType = ClientType String


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
