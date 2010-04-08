{-# LANGUAGE ScopedTypeVariables #-}
module Joy.Regexp (
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
import Prelude hiding (all, concat, elem, foldl)

import Joy.Automata
import Joy.Documentation
import Joy.EnumSet
import Joy.Uniqueness

import Debug.Trace


data (Ord content, Bounded content, Enum content) => Regexp content
    = EnumSetRegexp (EnumSet content)
    | Sequence [Regexp content]
    | Alternation [Regexp content]
    | ZeroOrOne (Regexp content)
    | ZeroOrMore (Regexp content)
    | OneOrMore (Regexp content)
    | Grouped (Regexp content)
    | NamedSubexpression String
    | PositiveLookahead (Regexp content)
    | NegativeLookahead (Regexp content)
    | PositiveLookbehind (Regexp content)
    | NegativeLookbehind (Regexp content)


instance (Ord content, Bounded content, Enum content) => Show (Regexp content) where
    show (EnumSetRegexp enumSet) = "EnumSet" ++ show enumSet
    show (Sequence regexps) = "Sequence " ++ show regexps
    show (Alternation regexps) = "Alternation " ++ show regexps
    show (ZeroOrOne regexp) = "ZeroOrOne (" ++ show regexp ++ ")"
    show (ZeroOrMore regexp) = "ZeroOrMore (" ++ show regexp ++ ")"
    show (OneOrMore regexp) = "OneOrMore (" ++ show regexp ++ ")"
    show (Grouped regexp) = "Grouped (" ++ show regexp ++ ")"
    show (NamedSubexpression identifier) = "NamedSubexpression " ++ identifier
    show (PositiveLookahead regexp) = "PositiveLookahead (" ++ show regexp ++ ")"
    show (NegativeLookahead regexp) = "NegativeLookahead (" ++ show regexp ++ ")"
    show (PositiveLookbehind regexp) = "PositiveLookbehind (" ++ show regexp ++ ")"
    show (NegativeLookbehind regexp) = "NegativeLookbehind (" ++ show regexp ++ ")"


data RegexpParseError = RegexpParseError String
instance Error RegexpParseError where
    strMsg string = RegexpParseError string
type RegexpParse = ErrorT RegexpParseError Identity


data (Ord content, Bounded content, Enum content) => RegexpChar content
    = Normal content | Special Char deriving (Show)


data RegexpScanState = NormalState | SetState | IdentifierState
                       deriving (Eq)


parseRegexp
    :: forall content . (Ord content, Bounded content, Enum content)
    => String
    -> Bool
    -> Either String (Regexp content)
parseRegexp input binaryMode =
    let parseRegexp' :: Int
                     -> [Regexp content]
                     -> [RegexpChar content]
                     -> RegexpParse ([Regexp content], [RegexpChar content])
        parseRegexp' 0 accumulator [] = return (reverse accumulator, [])
        parseRegexp' depth _ [] = fail $ "Unbalanced '(' in regexp"
        parseRegexp' depth accumulator
                     (Special '(' : Special '?' : Special '=' : rest) = do
          (recursiveResult, rest) <- parseRegexp' (depth+1) [] rest
          let accumulator' = (PositiveLookahead
                              $ mkSequenceRegexp recursiveResult) : accumulator
          parseRegexp' depth accumulator' rest
        parseRegexp' depth accumulator
                     (Special '(' : Special '?' : Special '!' : rest) = do
          (recursiveResult, rest) <- parseRegexp' (depth+1) [] rest
          let accumulator' = (NegativeLookahead
                              $ mkSequenceRegexp recursiveResult) : accumulator
          parseRegexp' depth accumulator' rest
        parseRegexp' depth accumulator
                     (Special '(' : Special '?' : Special '<' : Special '=' : rest) = do
          (recursiveResult, rest) <- parseRegexp' (depth+1) [] rest
          let accumulator' = (PositiveLookbehind
                              $ mkSequenceRegexp recursiveResult) : accumulator
          parseRegexp' depth accumulator' rest
        parseRegexp' depth accumulator
                     (Special '(' : Special '?' : Special '<' : Special '!' : rest) = do
          (recursiveResult, rest) <- parseRegexp' (depth+1) [] rest
          let accumulator' = (NegativeLookbehind
                              $ mkSequenceRegexp recursiveResult) : accumulator
          parseRegexp' depth accumulator' rest
        parseRegexp' depth accumulator (Special '(':rest) = do
          (recursiveResult, rest) <- parseRegexp' (depth+1) [] rest
          let accumulator' = (Grouped $ mkSequenceRegexp recursiveResult) : accumulator
          parseRegexp' depth accumulator' rest
        parseRegexp' 0 _ (Special ')':_)
            = fail $ "Unbalanced ')' in regexp"
        parseRegexp' depth accumulator (Special ')':rest)
            = return (reverse accumulator, rest)
        parseRegexp' depth accumulator (Special '[':Special '^':rest) = do
          (enumSet, rest) <- parseEnumSet emptyEnumSet rest
          enumSet <- if binaryMode
                       then return $ inverseEnumSet enumSet
                       else return $ differenceEnumSet printableEnumSet enumSet
          let accumulator' = (mkEnumSetRegexp enumSet) : accumulator
          parseRegexp' depth accumulator' rest
        parseRegexp' depth accumulator (Special '[':rest) = do
          (enumSet, rest) <- parseEnumSet emptyEnumSet rest
          let accumulator' = (mkEnumSetRegexp enumSet) : accumulator
          parseRegexp' depth accumulator' rest
        parseRegexp' depth _ (Special ']':_)
            = fail $ "Unbalanced ']' in regexp"
        parseRegexp' depth accumulator (Special '{':rest) = do
          (identifier, rest) <- parseIdentifier rest
          let accumulator' = (NamedSubexpression identifier) : accumulator
          parseRegexp' depth accumulator' rest
        parseRegexp' depth accumulator (Normal c:rest) = do
          let accumulator' = (mkSingletonRegexp c) : accumulator
          parseRegexp' depth accumulator' rest
        parseRegexp' depth accumulator (Special '.':rest) = do
          enumSet <- if binaryMode
                       then return fullEnumSet
                       else return printableEnumSet
          let accumulator' = (mkEnumSetRegexp enumSet) : accumulator
          parseRegexp' depth accumulator' rest
        parseRegexp' depth (mostRecent:older) (Special '?':rest) = do
          let accumulator' = (mkZeroOrOneRegexp mostRecent) : older
          parseRegexp' depth accumulator' rest
        parseRegexp' depth (mostRecent:older) (Special '*':rest) = do
          let accumulator' = (mkZeroOrMoreRegexp mostRecent) : older
          parseRegexp' depth accumulator' rest
        parseRegexp' depth (mostRecent:older) (Special '+':rest) = do
          let accumulator' = (mkOneOrMoreRegexp mostRecent) : older
          parseRegexp' depth accumulator' rest
        parseRegexp' depth firstChoice (Special '|':rest) = do
          (after, rest) <- parseRegexp' depth [] rest
          case after of
            [Alternation otherChoices] -> return $ ([Alternation
                                                     (Sequence (reverse firstChoice)
                                                      : otherChoices)],
                                                    rest)
            otherChoices -> return $ ([Alternation [Sequence (reverse firstChoice),
                                                    Sequence otherChoices]],
                                      rest)
        parseRegexp' depth [] (Special '?':rest) = fail $ "Nothing before '?' in regexp"
        parseRegexp' depth [] (Special '*':rest) = fail $ "Nothing before '*' in regexp"
        parseRegexp' depth [] (Special '+':rest) = fail $ "Nothing before '+' in regexp"
        
        parseEnumSet :: (EnumSet content)
                     -> [RegexpChar content]
                     -> RegexpParse (EnumSet content, [RegexpChar content])
        parseEnumSet enumSet (Normal start:Special '-':Normal end:rest)
            = parseEnumSet (unionEnumSet enumSet $ rangeEnumSet start end)
                           rest
        parseEnumSet enumSet (Special '-':rest)
            = fail $ "Invalid character '-' in character set in regexp"
        parseEnumSet enumSet (Special ']':rest) = return (enumSet, rest)
        parseEnumSet enumSet (Normal c:rest)
            = parseEnumSet (unionEnumSet enumSet $ enumerationEnumSet [c])
                           rest
        
        parseIdentifier :: [RegexpChar content]
                        -> RegexpParse (String, [RegexpChar content])
        parseIdentifier input = do
          let parseIdentifier' accumulator (Special '}':rest)
                  = return (reverse accumulator, rest)
              parseIdentifier' accumulator (Special c:rest)
                  = parseIdentifier' (c:accumulator) rest
          parseIdentifier' "" input
        
        fromChar :: Char -> content
        fromChar character = toEnum $ fromEnum character
        
        validHexEscape :: Int -> String -> Bool
        validHexEscape length input = all isHexDigit $ take length input
        
        readHexEscape :: Int -> String -> RegexpParse (content, String)
        readHexEscape length input =
            let value = fst $ head $ readHex $ take length input :: Integer
                rest = drop length input
            in if value > (fromIntegral $ fromEnum (maxBound :: content))
              then fail "Hex value out of range"
              else return (toEnum $ fromIntegral value, rest)
        
        printableEnumSet :: EnumSet content
        printableEnumSet = unionEnumSet (rangeEnumSet (fromChar ' ') (fromChar '~'))
                                        (if fromEnum (maxBound :: content) > 0x80
                                           then rangeEnumSet (toEnum 0x80) maxBound
                                           else emptyEnumSet)
        
        scanRegexpChar
            :: RegexpScanState
            -> String
            -> RegexpParse ([RegexpChar content], RegexpScanState, String)
        scanRegexpChar state ('\\':'\\':rest) | elem state [NormalState, SetState]
            = return ([Normal $ fromChar '\\'], state, rest)
        scanRegexpChar state ('\\':'n':rest) | elem state [NormalState, SetState]
            = return ([Normal $ fromChar '\n'], state, rest)
        scanRegexpChar state ('\\':'r':rest) | elem state [NormalState, SetState]
            = return ([Normal $ fromChar '\r'], state, rest)
        scanRegexpChar state ('\\':'f':rest) | elem state [NormalState, SetState]
            = return ([Normal $ fromChar '\f'], state, rest)
        scanRegexpChar state ('\\':'t':rest) | elem state [NormalState, SetState]
            = return ([Normal $ fromChar '\t'], state, rest)
        scanRegexpChar state ('\\':'v':rest) | elem state [NormalState, SetState]
            = return ([Normal $ fromChar '\v'], state, rest)
        scanRegexpChar NormalState ('\\':'.':rest)
            = return ([Normal $ fromChar '.'], NormalState, rest)
        scanRegexpChar NormalState ('\\':'+':rest)
            = return ([Normal $ fromChar '+'], NormalState, rest)
        scanRegexpChar NormalState ('\\':'*':rest)
            = return ([Normal $ fromChar '*'], NormalState, rest)
        scanRegexpChar NormalState ('\\':'?':rest)
            = return ([Normal $ fromChar '?'], NormalState, rest)
        scanRegexpChar NormalState ('\\':'|':rest)
            = return ([Normal $ fromChar '|'], NormalState, rest)
        scanRegexpChar NormalState ('\\':'(':rest)
            = return ([Normal $ fromChar '('], NormalState, rest)
        scanRegexpChar NormalState ('\\':')':rest)
            = return ([Normal $ fromChar ')'], NormalState, rest)
        scanRegexpChar NormalState ('\\':'{':rest)
            = return ([Normal $ fromChar '{'], NormalState, rest)
        scanRegexpChar NormalState ('\\':'}':rest)
            = return ([Normal $ fromChar '}'], NormalState, rest)
        scanRegexpChar SetState ('\\':'-':rest)
            = return ([Normal $ fromChar '-'], SetState, rest)
        scanRegexpChar state ('\\':'[':rest)
            = return ([Normal $ fromChar '['], state, rest)
        scanRegexpChar state ('\\':']':rest)
            = return ([Normal $ fromChar ']'], state, rest)
        scanRegexpChar state ('\\':'x':rest) | validHexEscape 2 rest = do
          (content, rest) <- readHexEscape 2 rest
          return ([Normal content], state, rest)
        scanRegexpChar state ('\\':'u':rest) | validHexEscape 4 rest = do
          (content, rest) <- readHexEscape 4 rest
          return ([Normal content], state, rest)
        scanRegexpChar state ('\\':'U':rest) | validHexEscape 8 rest = do
          (content, rest) <- readHexEscape 8 rest
          return ([Normal content], state, rest)
        scanRegexpChar _ ('\\':_) = fail $ "Invalid '\\' escape in regexp"
        scanRegexpChar NormalState ('.':rest)
            = return ([Special '.'], NormalState, rest)
        scanRegexpChar NormalState ('+':rest)
            = return ([Special '+'], NormalState, rest)
        scanRegexpChar NormalState ('*':rest)
            = return ([Special '*'], NormalState, rest)
        scanRegexpChar NormalState ('?':rest)
            = return ([Special '?'], NormalState, rest)
        scanRegexpChar NormalState ('|':rest)
            = return ([Special '|'], NormalState, rest)
        scanRegexpChar NormalState ('(':'?':'=':rest)
            = return ([Special '(', Special '?', Special '='], NormalState, rest)
        scanRegexpChar NormalState ('(':'?':'!':rest)
            = return ([Special '(', Special '?', Special '!'], NormalState, rest)
        scanRegexpChar NormalState ('(':'?':'<':'=':rest)
            = return ([Special '(', Special '?', Special '<', Special '='],
                      NormalState, rest)
        scanRegexpChar NormalState ('(':'?':'<':'!':rest)
            = return ([Special '(', Special '?', Special '<', Special '!'],
                      NormalState, rest)
        scanRegexpChar NormalState ('(':rest)
            = return ([Special '('], NormalState, rest)
        scanRegexpChar NormalState (')':rest)
            = return ([Special ')'], NormalState, rest)
        scanRegexpChar NormalState ('[':'^':rest)
            = return ([Special '[', Special '^'], SetState, rest)
        scanRegexpChar NormalState ('[':rest)
            = return ([Special '['], SetState, rest)
        scanRegexpChar NormalState (']':rest)
            = fail $ "Unbalanced ']' in regexp"
        scanRegexpChar SetState ('[':rest)
            = fail $ "Invalid character '[' in character set in regexp"
        scanRegexpChar SetState (']':rest)
            = return ([Special ']'], NormalState, rest)
        scanRegexpChar SetState ('-':rest)
            = return ([Special '-'], SetState, rest)
        scanRegexpChar NormalState ('{':rest)
            = return ([Special '{'], IdentifierState, rest)
        scanRegexpChar IdentifierState ('}':rest)
            = return ([Special '}'], NormalState, rest)
        scanRegexpChar IdentifierState (c:rest) | isAlpha c
            = return ([Special c], IdentifierState, rest)
        scanRegexpChar state (c:rest) = return ([Normal $ fromChar c], state, rest)
        
        scanRegexpChars :: RegexpScanState -> String -> RegexpParse [RegexpChar content]
        scanRegexpChars NormalState "" = return []
        scanRegexpChars SetState "" = fail $ "Unbalanced '[' in regexp"
        scanRegexpChars IdentifierState "" = fail $ "Unbalanced '{' in regexp"
        scanRegexpChars state input = do
          (outputHere, state, rest) <- scanRegexpChar state input
          outputRest <- scanRegexpChars state rest
          return $ outputHere ++ outputRest
        
        parseAll :: RegexpParse (Regexp content)
        parseAll = do
          regexpString <- scanRegexpChars NormalState input
          (result, _) <- parseRegexp' 0 [] regexpString
          case result of
            [] -> fail "Empty regexp"
            _ -> return $ mkSequenceRegexp result
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
    :: forall m content stateData
       . (MonadUnique m, Ord content, Bounded content, Enum content)
    => (Regexp content)
    -> (Map String (Regexp content, Maybe stateData))
    -> (Int, stateData)
    -> m (NFA (EnumSet content) (Maybe (Int, stateData)) ())
regexpToNFA regexp subexpressionBindingMap datum = do
    let regexpToNFA' :: (NFA (EnumSet content) (Maybe (Int, stateData)) (), [UniqueID])
                     -> (Regexp content)
                     -> [String]
                     -> m (NFA (EnumSet content) (Maybe (Int, stateData)) (), [UniqueID])
        regexpToNFA' (nfa, tailStates) (Grouped regexp) visited = do
          (nfa, tailStates) <- regexpToNFA' (nfa, tailStates) regexp visited
          return (nfa, tailStates)
        regexpToNFA' (nfa, tailStates) (EnumSetRegexp enumSet) visited = do
          (nfa, newState) <- automatonAddState nfa Nothing
          let nfa' = foldl (\nfa tailState -> automatonAddTransition nfa
                                                                     tailState
                                                                     newState
                                                                     enumSet
                                                                     ())
                           nfa
                           tailStates
          return (nfa', [newState])
        regexpToNFA' (nfa, initialTailStates) (Sequence regexps) visited = do
          foldlM (\(nfa, tailStates) regexp
                      -> regexpToNFA' (nfa, tailStates) regexp visited)
                 (nfa, initialTailStates)
                 regexps
        regexpToNFA' (nfa, initialTailStates) (Alternation regexps) visited = do
          foldlM (\(nfa, tailStates) regexp -> do
                   (nfa, newTailStates) <- regexpToNFA' (nfa, initialTailStates)
                                                        regexp
                                                        visited
                   return (nfa, concat [tailStates, newTailStates]))
                 (nfa, [])
                 regexps
        regexpToNFA' (nfa, initialTailStates) (ZeroOrOne regexp) visited = do
          (nfa', newTailStates) <- regexpToNFA' (nfa, initialTailStates) regexp visited
          return $ (nfa', concat [initialTailStates, newTailStates])
        regexpToNFA' (nfa, initialTailStates) (ZeroOrMore regexp) visited = do
          let exampleTailState = head initialTailStates
              preexistingTransitions = automatonTransitionMap nfa exampleTailState
          (nfa, newTailStates) <- regexpToNFA' (nfa, initialTailStates) regexp visited
          let newTransitions = automatonTransitionMap nfa exampleTailState
              exampleTransitions = newTransitions Map.\\ preexistingTransitions
              nfa' = foldl (\nfa (enumSet, resultingStates) ->
                             foldl (\nfa tailState ->
                                     foldl (\nfa resultingState ->
                                             automatonAddTransition nfa
                                                                    tailState
                                                                    resultingState
                                                                    enumSet
                                                                    ())
                                           nfa
                                           $ map fst resultingStates)
                                   nfa
                                   newTailStates)
                           nfa
                           $ Map.toList exampleTransitions
          return $ (nfa', concat [initialTailStates, newTailStates])
        regexpToNFA' (nfa, initialTailStates) (OneOrMore regexp) visited = do
          let exampleTailState = head initialTailStates
              preexistingTransitions = automatonTransitionMap nfa exampleTailState
          (nfa, newTailStates) <- regexpToNFA' (nfa, initialTailStates) regexp visited
          let newTransitions = automatonTransitionMap nfa exampleTailState
              exampleTransitions = newTransitions Map.\\ preexistingTransitions
              nfa' = foldl (\nfa (enumSet, resultingStates) ->
                             foldl (\nfa tailState ->
                                     foldl (\nfa resultingState ->
                                             automatonAddTransition nfa
                                                                    tailState
                                                                    resultingState
                                                                    enumSet
                                                                    ())
                                           nfa
                                           $ map fst resultingStates)
                                   nfa
                                   newTailStates)
                           nfa
                           $ Map.toList exampleTransitions
          return (nfa', newTailStates)
        regexpToNFA' (nfa, initialTailStates)
                     (NamedSubexpression identifier)
                     visited = do
          if elem identifier visited
            then fail $ "Recursive subexpressions in regexp: "
                        ++ (englishList $ visited ++ [identifier])
            else do
              let maybeSubexpression = Map.lookup identifier subexpressionBindingMap
              case maybeSubexpression of
                Nothing -> fail $ "Subexpression " ++ identifier ++ " not found."
                Just (subexpression, maybeExpression) -> do
                  regexpToNFA' (nfa, initialTailStates)
                               subexpression
                               (visited ++ [identifier])
        regexpToNFA' (nfa, initialTailStates) regexp visited = do
          trace (show regexp) (return (nfa, initialTailStates))
    emptyNFA <- emptyAutomaton Nothing
    (fullNFA, fullNFATailStates) <- regexpToNFA' (emptyNFA, automatonStates emptyNFA)
                                                 regexp
                                                 []
    fullNFA <- foldlM (\nfa tailState -> do
                        let nfa' = automatonSetStateAccepting nfa tailState True
                            nfa'' = automatonSetStateData nfa' tailState $ Just datum
                        return nfa'')
                      fullNFA
                      fullNFATailStates
    return $ fullNFA
