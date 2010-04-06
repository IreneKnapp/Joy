module Joy.Documentation (
                          LineNumber(..),
                          Located(..),
                          englishList
                         )
    where

import Data.List
import Data.Word


type LineNumber = Word64


class Located a where
    location :: a -> LineNumber


englishList :: [String] -> String
englishList [] = ""
englishList [item] = item
englishList (a:b:[]) = a ++ " and " ++ b
englishList items = (intercalate ", " $ reverse $ drop 1 $ reverse items)
                    ++ ", and "
                    ++ (head $ reverse items)
