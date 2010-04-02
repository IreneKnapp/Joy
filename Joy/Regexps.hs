module Joy.Regexps (
                    Regexp,
                    parseRegexp,
                    mkSingletonRegexp,
                    mkEnumSetRegexp,
                    mkStringRegexp,
                    mkSequenceRegexp,
                    mkAlternationRegexp,
                    mkZeroOrOneRegexp,
                    mkZeroOrMoreRegexp,
                    mkOneOrMoreRegexp,
                    regexpToNFA
                   )
    where

import Control.Monad.Error
import Control.Monad.Identity
import Data.Char
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Numeric
import Prelude hiding (all, concat, foldl)

import Joy.Automata
import Joy.EnumSets
import Joy.Uniqueness

data (Ord content, Bounded content, Enum content) => Regexp content
    = EnumSetRegexp (EnumSet content)
    | Sequence [Regexp content]
    | Alternation [Regexp content]
    | ZeroOrOne (Regexp content)
    | ZeroOrMore (Regexp content)
    | OneOrMore (Regexp content)
    | Grouped (Regexp content)


data RegexpParseError = RegexpParseError String
instance Error RegexpParseError where
    strMsg string = RegexpParseError string
type RegexpParse = ErrorT RegexpParseError Identity


parseRegexp
    :: (Ord content, Bounded content, Enum content)
    => String
    -> Either String (Regexp content)
parseRegexp input =
    let parseRegexp' :: (Ord content, Bounded content, Enum content)
                     => Int
                     -> String
                     -> RegexpParse (Maybe (Regexp content), String)
        parseRegexp' 0 "" = return (Nothing, "")
        parseRegexp' depth "" = fail $ "Unbalanced '(' in regexp"
        parseRegexp' depth ('\\':'\\':rest) = catR (mkSingletonRegexp $ fromChar '\\')
                                                   $ parseRegexp' depth rest
        parseRegexp' depth ('\\':'n':rest) = catR (mkSingletonRegexp $ fromChar '\n')
                                                  $ parseRegexp' depth rest
        parseRegexp' depth ('\\':'r':rest) = catR (mkSingletonRegexp $ fromChar '\r')
                                                  $ parseRegexp' depth rest
        parseRegexp' depth ('\\':'f':rest) = catR (mkSingletonRegexp $ fromChar '\f')
                                                  $ parseRegexp' depth rest
        parseRegexp' depth ('\\':'t':rest) = catR (mkSingletonRegexp $ fromChar '\t')
                                                  $ parseRegexp' depth rest
        parseRegexp' depth ('\\':'v':rest) = catR (mkSingletonRegexp $ fromChar '\v')
                                                  $ parseRegexp' depth rest
        parseRegexp' depth ('\\':'+':rest) = catR (mkSingletonRegexp $ fromChar '+')
                                                  $ parseRegexp' depth rest
        parseRegexp' depth ('\\':'*':rest) = catR (mkSingletonRegexp $ fromChar '*')
                                                  $ parseRegexp' depth rest
        parseRegexp' depth ('\\':'(':rest) = catR (mkSingletonRegexp $ fromChar '(')
                                                  $ parseRegexp' depth rest
        parseRegexp' depth ('\\':')':rest) = catR (mkSingletonRegexp $ fromChar '(')
                                                  $ parseRegexp' depth rest
        parseRegexp' depth ('\\':'[':rest) = catR (mkSingletonRegexp $ fromChar '[')
                                                  $ parseRegexp' depth rest
        parseRegexp' depth ('\\':']':rest) = catR (mkSingletonRegexp $ fromChar ']')
                                                  $ parseRegexp' depth rest
        parseRegexp' depth ('\\':'x':rest) | validHexEscape 2 rest
            = let (content, rest) = readHexEscape 2 rest
              in catR (mkSingletonRegexp content) $ parseRegexp' depth rest
        parseRegexp' depth ('\\':'u':rest) | validHexEscape 4 rest
            = let (content, rest) = readHexEscape 4 rest
              in catR (mkSingletonRegexp content) $ parseRegexp' depth rest
        parseRegexp' depth ('\\':'U':rest) | validHexEscape 8 rest
            = let (content, rest) = readHexEscape 8 rest
              in catR (mkSingletonRegexp content) $ parseRegexp' depth rest
        parseRegexp' depth ('\\':rest) = fail $ "Invalid '\\' escape in regexp"
        parseRegexp' depth ('[':'^':rest) = do
          (enumSet, rest) <- parseEnumSet emptyEnumSet rest
          catR (mkEnumSetRegexp $ inverseEnumSet enumSet)
               $ parseRegexp' depth rest
        parseRegexp' depth ('[':rest) = do
          (enumSet, rest) <- parseEnumSet emptyEnumSet rest
          catR (mkEnumSetRegexp enumSet)
               $ parseRegexp' depth rest
        parseRegexp' depth (']':rest) = fail $ "Unbalanced ']' in regexp"
        parseRegexp' depth ('(':rest) = do
          recursiveResult <- parseRegexp' (depth+1) rest
          case recursiveResult of
            (Nothing, rest) -> return (Just $ Grouped (Sequence []), rest)
            (Just regexp, rest) -> return (Just $ Grouped regexp, rest)
        parseRegexp' 0 (')':rest) = fail $ "Unbalanced ')' in regexp"
        parseRegexp' depth (')':rest) = return (Nothing, rest)
        parseRegexp' depth (c:rest) = catR (mkSingletonRegexp $ fromChar c)
                                           $ parseRegexp' depth rest
        
        catR :: (Ord content, Bounded content, Enum content)
             => (Regexp content)
             -> RegexpParse (Maybe (Regexp content), String)
             -> RegexpParse (Maybe (Regexp content), String)
        catR regexpA action = do
          actionResult <- action
          case actionResult of
            (Nothing, rest) -> return (Just regexpA, rest)
            (Just regexpB, rest)
                -> return (Just $ mkSequenceRegexp [regexpA, regexpB], rest)
        
        parseEnumSet :: (Ord content, Bounded content, Enum content)
                     => (EnumSet content)
                     -> String
                     -> RegexpParse (EnumSet content, String)
        parseEnumSet enumSet (start:'-':end:rest)
            = parseEnumSet (unionEnumSet enumSet
                                         $ rangeEnumSet (fromChar start)
                                                        (fromChar end))
                           rest
        parseEnumSet enumSet ('\\':'-':rest)
            = parseEnumSet (unionEnumSet enumSet $ enumerationEnumSet [fromChar '-'])
                           rest
        parseEnumSet enumSet ('[':rest)
            = fail $ "Invalid character '[' in character set in regexp"
        parseEnumSet enumSet ('-':rest)
            = fail $ "Invalid character '-' in character set in regexp"
        parseEnumSet enumSet (']':rest) = return (enumSet, rest)
        parseEnumSet enumSet (c:rest)
            = parseEnumSet (unionEnumSet enumSet $ enumerationEnumSet [fromChar c])
                           rest
        
        fromChar :: (Ord content, Bounded content, Enum content)
                 => Char
                 -> content
        fromChar character = toEnum $ fromEnum character
        
        validHexEscape :: Int -> String -> Bool
        validHexEscape length input = all isHexDigit $ take length input
        
        readHexEscape :: (Ord content, Bounded content, Enum content)
                      => Int -> String -> (content, String)
        readHexEscape length input = (toEnum $ fst $ head $ readHex $ take length input,
                                      drop length input)
        
        parseAll :: (Ord content, Bounded content, Enum content)
                 => RegexpParse (Regexp content)
        parseAll = do
          result <- parseRegexp' 0 input
          case result of
            (Nothing, _) -> fail "Empty regexp"
            (Just regexp, _) -> return regexp
    in case runIdentity $ runErrorT parseAll of
         Left (RegexpParseError message) -> Left message
         Right result -> Right result


mkSingletonRegexp
    :: (Ord content, Bounded content, Enum content)
    => content
    -> (Regexp content)
mkSingletonRegexp content = EnumSetRegexp $ enumerationEnumSet [content]


mkEnumSetRegexp
    :: (Ord content, Bounded content, Enum content)
    => (EnumSet content)
    -> (Regexp content)
mkEnumSetRegexp enumSet = EnumSetRegexp enumSet


mkStringRegexp
    :: (Ord content, Bounded content, Enum content)
    => [content]
    -> (Regexp content)
mkStringRegexp content = Sequence $ map mkSingletonRegexp content


mkSequenceRegexp
    :: (Ord content, Bounded content, Enum content)
    => [Regexp content]
    -> (Regexp content)
mkSequenceRegexp regexps = Sequence regexps


mkAlternationRegexp
    :: (Ord content, Bounded content, Enum content)
    => [Regexp content]
    -> (Regexp content)
mkAlternationRegexp regexps = Alternation regexps


mkZeroOrOneRegexp
    :: (Ord content, Bounded content, Enum content)
    => (Regexp content)
    -> (Regexp content)
mkZeroOrOneRegexp regexp = ZeroOrOne regexp


mkZeroOrMoreRegexp
    :: (Ord content, Bounded content, Enum content)
    => (Regexp content)
    -> (Regexp content)
mkZeroOrMoreRegexp regexp = ZeroOrMore regexp


mkOneOrMoreRegexp
    :: (Ord content, Bounded content, Enum content)
    => (Regexp content)
    -> (Regexp content)
mkOneOrMoreRegexp regexp = OneOrMore regexp


regexpToNFA
    :: (MonadUnique m, Ord content, Bounded content, Enum content)
    => (Regexp content)
    -> data'
    -> m (NFA (EnumSet content) (Maybe data'))
regexpToNFA regexp datum = do
    let regexpToNFA' :: (MonadUnique m, Ord content, Bounded content, Enum content)
                     => (NFA (EnumSet content) (Maybe data'), [UniqueID])
                     -> (Regexp content)
                     -> m (NFA (EnumSet content) (Maybe data'), [UniqueID])
        regexpToNFA' (nfa, tailStates) (EnumSetRegexp enumSet) = do
          (nfa, newState) <- automatonAddState nfa Nothing
          let nfa' = foldl (\nfa tailState -> automatonAddTransition nfa
                                                                     tailState
                                                                     newState
                                                                     enumSet)
                           nfa
                           tailStates
          return (nfa', [newState])
        regexpToNFA' (nfa, initialTailStates) (Sequence regexps) = do
          foldlM regexpToNFA'
                 (nfa, initialTailStates)
                 regexps
        regexpToNFA' (nfa, initialTailStates) (Alternation regexps) = do
          foldlM (\(nfa, tailStates) regexp -> do
                   (nfa, newTailStates) <- regexpToNFA' (nfa, initialTailStates) regexp
                   return (nfa, concat [tailStates, newTailStates]))
                 (nfa, [])
                 regexps
        regexpToNFA' (nfa, initialTailStates) (ZeroOrOne regexp) = do
          (nfa', newTailStates) <- regexpToNFA' (nfa, initialTailStates) regexp
          return $ (nfa', concat [initialTailStates, newTailStates])
        regexpToNFA' (nfa, initialTailStates) (ZeroOrMore regexp) = do
          let exampleTailState = head initialTailStates
              preexistingTransitions = automatonTransitionMap nfa exampleTailState
          (nfa, newTailStates) <- regexpToNFA' (nfa, initialTailStates) regexp
          let newTransitions = automatonTransitionMap nfa exampleTailState
              exampleTransitions = newTransitions Map.\\ preexistingTransitions
              nfa' = foldl (\nfa (enumSet, resultingStates) ->
                             foldl (\nfa tailState ->
                                     foldl (\nfa resultingState ->
                                             automatonAddTransition nfa
                                                                    tailState
                                                                    resultingState
                                                                    enumSet)
                                           nfa
                                           $ Set.toList resultingStates)
                                   nfa
                                   newTailStates)
                           nfa
                           $ Map.toList exampleTransitions
          return $ (nfa', concat [initialTailStates, newTailStates])
        regexpToNFA' (nfa, initialTailStates) (OneOrMore regexp) = do
          let exampleTailState = head initialTailStates
              preexistingTransitions = automatonTransitionMap nfa exampleTailState
          (nfa, newTailStates) <- regexpToNFA' (nfa, initialTailStates) regexp
          let newTransitions = automatonTransitionMap nfa exampleTailState
              exampleTransitions = newTransitions Map.\\ preexistingTransitions
              nfa' = foldl (\nfa (enumSet, resultingStates) ->
                             foldl (\nfa tailState ->
                                     foldl (\nfa resultingState ->
                                             automatonAddTransition nfa
                                                                    tailState
                                                                    resultingState
                                                                    enumSet)
                                           nfa
                                           $ Set.toList resultingStates)
                                   nfa
                                   newTailStates)
                           nfa
                           $ Map.toList exampleTransitions
          return (nfa', newTailStates)
    emptyNFA <- emptyAutomaton Nothing
    (fullNFA, fullNFATailStates) <- regexpToNFA' (emptyNFA, automatonStates emptyNFA)
                                                 regexp
    fullNFA <- foldlM (\nfa tailState -> do
                        let nfa' = automatonSetAccepting nfa tailState True
                            nfa'' = automatonSetData nfa' tailState $ Just datum
                        return nfa'')
                      fullNFA
                      fullNFATailStates
    return $ fullNFA
