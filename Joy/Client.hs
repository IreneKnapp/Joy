module Joy.Client (
                   ClientRaw(..),
                   ClientType(..),
                   ClientPattern(..),
                   ClientIdentifier(..),
                   ClientExpression(..),
                   ClientAction(..),
                   clientExpressionSubstitute,
                   clientActionSubstitute,
                   clientPatternSubstituteWildcard,
                   clientPatternSubstituteName
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


data ClientAction = ClientAction String


clientExpressionSubstitute :: ClientExpression -> String
clientExpressionSubstitute (ClientExpression input) = substituteNumeric input


clientActionSubstitute :: ClientAction -> String
clientActionSubstitute (ClientAction input) = substituteNumeric input


substituteNumeric :: String -> String
substituteNumeric input =
  let substitute "" = ""
      substitute ('$':rest) =
        let (firstWord, rest') = maybe ("", rest)
                                       (\point -> splitAt point rest)
                                       $ case elemIndex ' ' rest of
                                           Just index -> Just index
                                           Nothing -> Just $ length rest
            maybeIndex = if (length firstWord > 0) && (all isDigit firstWord)
                           then Just $ (read firstWord :: Int)
                           else Nothing
        in case maybeIndex of
             Nothing -> "$" ++ firstWord ++ substitute rest'
             Just index -> "joy_" ++ (show index) ++ substitute rest'
      substitute (c:rest) = c : substitute rest
  in substitute input


clientPatternSubstituteWildcard :: ClientPattern -> String
clientPatternSubstituteWildcard (ClientPattern input) =
  let substitute "" = ""
      substitute ('$':'$':rest) = '_' : substitute rest
      substitute (c:rest) = c : substitute rest
  in substitute input


clientPatternSubstituteName :: ClientPattern -> String -> String
clientPatternSubstituteName (ClientPattern input) name =
  let substitute "" = ("", False)
      substitute ('$':'$':rest) = let (rest', _) = substitute rest
                                  in (name ++ rest', True)
      substitute (c:rest) = let (rest', result) = substitute rest
                            in (c : rest', result)
      (output, foundAny) = substitute input
  in if foundAny
       then "(" ++ output ++ ")"
       else name ++ "@(" ++ output ++ ")"
