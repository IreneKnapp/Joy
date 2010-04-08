module Joy.Documentation (
                          LineNumber(..),
                          Located(..),
                          trim,
                          englishList,
                          filePathFileComponent
                         )
    where

import Data.Char
import Data.List
import Data.Word


type LineNumber = Word64


class Located a where
    location :: a -> LineNumber


trim :: String -> String
trim string = dropWhile isSpace $ reverse $ dropWhile isSpace $ reverse string


englishList :: [String] -> String
englishList [] = ""
englishList [item] = item
englishList (a:b:[]) = a ++ " and " ++ b
englishList items = (intercalate ", " $ reverse $ drop 1 $ reverse items)
                    ++ ", and "
                    ++ (head $ reverse items)


filePathFileComponent :: FilePath -> Maybe String
filePathFileComponent path =
    let totalLength = length path
        slashPoint = maybe 0 (\index -> totalLength - index)
                           $ elemIndex '/' $ reverse path
    in if slashPoint == totalLength
      then Nothing
      else Just $ drop slashPoint path
