{-# LANGUAGE ExistentialQuantification #-}
module Joy.EnumSets (
                     EnumSet,
                     enumInSet,
                     emptyEnumSet,
                     fullEnumSet,
                     rangeEnumSet,
                     enumerationEnumSet,
                     negativeEnumerationEnumSet,
                     unionEnumSet,
                     differenceEnumSet,
                     relevantSubsetsForEnumSets,
                     anyEnumInSet
                    )
    where

import Data.List
import Data.Maybe


data EnumSet content
    = (Ord content, Bounded content, Enum content)
      => EnumSet [(content, content)]


enumInSet :: (EnumSet content) -> content -> Bool
enumInSet (EnumSet ranges) enum
    = let enumInRange (start, end) =
              (fromEnum start <= fromEnum enum) && (fromEnum enum <= fromEnum end)
      in any enumInRange ranges


emptyEnumSet :: (Ord content, Bounded content, Enum content)
                => EnumSet content
emptyEnumSet = EnumSet []


fullEnumSet :: (Ord content, Bounded content, Enum content)
               => EnumSet content
fullEnumSet = EnumSet [(minBound, maxBound)]


rangeEnumSet :: (Ord content, Bounded content, Enum content)
                => content -> content -> EnumSet content
rangeEnumSet start end = EnumSet [(start, end)]


enumerationEnumSet :: (Ord content, Bounded content, Enum content)
                      => [content] -> EnumSet content
enumerationEnumSet enums
    = foldl addEnumToSet emptyEnumSet enums


negativeEnumerationEnumSet :: (Ord content, Bounded content, Enum content)
                              => [content] -> EnumSet content
negativeEnumerationEnumSet enums
    = foldl removeEnumFromSet fullEnumSet enums


unionEnumSet :: (EnumSet content) -> (EnumSet content) -> (EnumSet content)
unionEnumSet (EnumSet rangesA) (EnumSet rangesB)
    = EnumSet $ unionRangeSets rangesA rangesB


differenceEnumSet :: (EnumSet content) -> (EnumSet content) -> (EnumSet content)
differenceEnumSet (EnumSet rangesA) (EnumSet rangesB)
    = EnumSet $ subtractRangeSets rangesA rangesB


addEnumToSet :: (EnumSet content) -> content -> (EnumSet content)
addEnumToSet (EnumSet ranges) enum
    = EnumSet $ unionRangeSets ranges [(enum, enum)]


removeEnumFromSet :: (EnumSet content) -> content -> (EnumSet content)
removeEnumFromSet (EnumSet ranges) enum
    = EnumSet $ subtractRangeSets ranges [(enum, enum)]


findLastStartingBefore
    :: (Ord content, Bounded content, Enum content)
    => [(content, content)]
    -> (content, content)
    -> Bool
    -> (Maybe Int, Bool)
findLastStartingBefore ranges newRange joinAdjacent
    = let maybeIndex = case ranges of
                         [] -> Nothing
                         (firstRange:_) | fst newRange < fst firstRange -> Nothing
                         _ -> foldl (\lastResult (range, i)
                                         -> if fst range <= fst newRange
                                              then Just i
                                              else lastResult)
                                    Nothing
                                    $ zip ranges [0..]
          intersects = maybe False
                             (\index -> ((fromEnum $ fst newRange)
                                         - (fromEnum $ snd $ head $ drop index ranges))
                                        <= (if joinAdjacent then 1 else 0))
                             maybeIndex
      in (maybeIndex, intersects)


findFirstEndingAfter
    :: (Ord content, Bounded content, Enum content)
    => [(content, content)]
    -> (content, content)
    -> Bool
    -> (Maybe Int, Bool)
findFirstEndingAfter ranges newRange joinAdjacent
    = let maybeLengthMinusIndex
              = case reverse ranges of
                  [] -> Nothing
                  (lastRange:_) | snd lastRange < snd newRange -> Nothing
                  reversedRanges -> foldl (\lastResult (range, i)
                                               -> if snd newRange <= snd range
                                                    then Just i
                                                    else lastResult)
                                          Nothing
                                          $ zip reversedRanges [0..]
          maybeIndex
              = maybe Nothing
                      (\index -> Just $ length ranges - index - 1)
                      maybeLengthMinusIndex
          intersects = maybe False
                             (\index -> ((fromEnum $ fst $ head $ drop index ranges)
                                         - (fromEnum $ snd newRange))
                                        <= (if joinAdjacent then 1 else 0))
                             maybeIndex
      in (maybeIndex, intersects)


findStartAndEndInformation
    :: (Ord content, Bounded content, Enum content)
    => [(content, content)]
    -> (content, content)
    -> Bool
    -> (Maybe Int, Bool, Maybe Int, Bool)
findStartAndEndInformation ranges newRange joinAdjacent
    = let (maybeStartIndex, startIntersects)
              = findLastStartingBefore ranges newRange joinAdjacent
          (maybeEndIndex, endIntersects)
              = findFirstEndingAfter ranges newRange joinAdjacent
      in (maybeStartIndex, startIntersects, maybeEndIndex, endIntersects)


addRangeToSet
    :: (Ord content, Bounded content, Enum content)
    => [(content, content)]
    -> (content, content)
    -> [(content, content)]
addRangeToSet ranges newRange
    = let (maybeStartIndex, startIntersects, maybeEndIndex, endIntersects)
              = findStartAndEndInformation ranges newRange True
      in if (isNothing maybeStartIndex) && (isNothing maybeEndIndex)
           then [newRange]
           else concat [maybe []
                              (\startIndex -> take (if startIntersects
                                                      then startIndex
                                                      else startIndex + 1)
                                                   ranges)
                              maybeStartIndex,
                        [(if startIntersects
                            then fst $ head $ drop (fromJust maybeStartIndex) ranges
                            else fst newRange,
                          if endIntersects
                            then snd $ head $ drop (fromJust maybeEndIndex) ranges
                            else snd newRange)],
                        maybe []
                              (\endIndex -> drop (if endIntersects
                                                    then endIndex + 1
                                                    else endIndex)
                                                 ranges)
                              maybeEndIndex]


subtractRangeFromSet
    :: (Ord content, Bounded content, Enum content)
    => [(content, content)]
    -> (content, content)
    -> [(content, content)]
subtractRangeFromSet ranges newRange
    = let (maybeStartIndex, startIntersects, maybeEndIndex, endIntersects)
              = findStartAndEndInformation ranges newRange True
      in if (isNothing maybeStartIndex) && (isNothing maybeEndIndex)
           then []
           else concat [maybe []
                              (\startIndex -> take (if startIntersects
                                                      then startIndex
                                                      else startIndex + 1)
                                                   ranges)
                              maybeStartIndex,
                        if startIntersects
                           && (fst newRange
                               > (fst $ head $ drop (fromJust maybeStartIndex) ranges))
                          then [(fst $ head $ drop (fromJust maybeStartIndex) ranges,
                                 toEnum $ (fromEnum $ fst newRange) - 1)]
                          else [],
                        if endIntersects
                           && ((snd $ head $ drop (fromJust maybeEndIndex) ranges)
                               > snd newRange)
                          then [(toEnum $ (fromEnum $ snd newRange) + 1,
                                 snd $ head $ drop (fromJust maybeEndIndex) ranges)]
                          else [],
                        maybe []
                              (\endIndex -> drop (if endIntersects
                                                    then endIndex + 1
                                                    else endIndex)
                                                 ranges)
                              maybeEndIndex]


overlappingRangeParts
    :: (Ord content, Bounded content, Enum content)
    => [(content, content)]
    -> (content, content)
    -> [(content, content)]
overlappingRangeParts ranges newRange
    = let (maybeStartIndex, startIntersects, maybeEndIndex, endIntersects)
              = findStartAndEndInformation ranges newRange False
      in case (maybeStartIndex, maybeEndIndex) of
        (Nothing, Nothing) -> []
        (Just a, Just b) | a == b -> [newRange]
        _ -> concat [maybe []
                           (\startIndex
                                -> if startIntersects
                                     then [(fst newRange,
                                            snd $ head $ drop startIndex ranges)]
                                     else [])
                           maybeStartIndex,
                     let rangeStart = maybe 0 (1+) maybeStartIndex
                         rangeEnd = maybe (length ranges) id maybeEndIndex
                         nToTake = rangeEnd - rangeStart
                         nToDrop = rangeStart
                     in take nToTake $ drop nToDrop ranges,
                     maybe []
                           (\endIndex
                                -> if endIntersects
                                     then [(fst $ head $ drop endIndex ranges,
                                            snd newRange)]
                                     else [])
                           maybeEndIndex]


nonOverlappingRangeParts
    :: (Ord content, Bounded content, Enum content)
    => [(content, content)]
    -> (content, content)
    -> [(content, content)]
nonOverlappingRangeParts ranges newRange
    = foldl (\result overlappingPart -> subtractRangeFromSet result overlappingPart)
            [newRange]
            $ overlappingRangeParts ranges newRange


intersectRangeSets
    :: (Ord content, Bounded content, Enum content)
    => [(content, content)]
    -> [(content, content)]
    -> [(content, content)]
intersectRangeSets a b
    = foldl (\result range -> foldl (\result part -> addRangeToSet result part)
                                    result
                                    $ overlappingRangeParts a range)
            []
            b


unionRangeSets
    :: (Ord content, Bounded content, Enum content)
    => [(content, content)]
    -> [(content, content)]
    -> [(content, content)]
unionRangeSets a b
    = foldl (\result range -> addRangeToSet result range)
            a
            b


subtractRangeSets
    :: (Ord content, Bounded content, Enum content)
    => [(content, content)]
    -> [(content, content)]
    -> [(content, content)]
subtractRangeSets a b
    = foldl (\result range -> subtractRangeFromSet result range)
            a
            b


exclusiveOrRangeSets
    :: (Ord content, Bounded content, Enum content)
    => [(content, content)]
    -> [(content, content)]
    -> [(content, content)]
exclusiveOrRangeSets a b
    = let result = foldl (\result range
                              -> foldl (\result part -> addRangeToSet result part)
                                       result
                                       $ nonOverlappingRangeParts b range)
                         []
                         a
          result' = foldl (\result range
                               -> foldl (\result part -> addRangeToSet result part)
                                        result
                                        $ nonOverlappingRangeParts a range)
                          result
                          b
      in result'


{-

<            |====|====|    |    |           >   (A B)
<            |    |====|    |====|           >   (B D)
union to
<            |====|====|    |====|           >   (A B D) -- union
difference to
<            |====|    |    |    |           >   (A) -- difference
intersect to
<            |    |====|    |    |           >   (B) -- intersect
xor to
<            |====|    |    |====|           >   (A D) -- xor

-}

relevantSubsetsForEnumSets
    :: (Ord content, Bounded content, Enum content)
    => [EnumSet content]
    -> [EnumSet content]
relevantSubsetsForEnumSets sets =
    let computeBoundaries f
            = sort $ nub $ concat $ map (\(EnumSet ranges) -> map f ranges)
                                        sets
        startBoundaries = computeBoundaries fst
        endBoundaries = computeBoundaries snd
        startBoundariesMinusOne
            = mapMaybe (\i -> if i > minBound
                                then Just $ toEnum $ (-1+) $ fromEnum i
                                else Nothing)
                       startBoundaries
        endBoundariesPlusOne = mapMaybe (\i -> if i < maxBound
                                                 then Just $ toEnum $ (1+) $ fromEnum i
                                                 else Nothing)
                                        endBoundaries
        allBoundaries
            = sort $ concat [startBoundaries,
                             endBoundaries,
                             filter (\i -> not $ elem i endBoundaries)
                                    startBoundariesMinusOne,
                             filter (\i -> not $ elem i startBoundaries)
                                    endBoundariesPlusOne]
        nToDropFromStart = if elem minBound startBoundaries
                             then 0
                             else 1
        nToDropFromEnd = if elem maxBound endBoundaries
                           then 0
                           else 1
        allBoundariesWithoutEndpoints
            = drop nToDropFromStart
              $ reverse
              $ drop nToDropFromEnd
              $ reverse allBoundaries
        allBoundariesEvenIndices
            = map fst $ filter (even . snd) $ zip allBoundariesWithoutEndpoints [0..]
        allBoundariesOddIndices
            = map fst $ filter (odd . snd) $ zip allBoundariesWithoutEndpoints [0..]
    in map (\range -> EnumSet [range])
           $ zip allBoundariesEvenIndices allBoundariesOddIndices


anyEnumInSet :: EnumSet content -> Maybe content
anyEnumInSet (EnumSet ((result, _):_)) = Just result
anyEnumInSet _ = Nothing


instance Eq (EnumSet content) where
    (EnumSet aRanges) == (EnumSet bRanges)
        = aRanges == bRanges
