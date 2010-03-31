{
module Joy.Specification (
                          readSpecificationFile
                         )
    where

import Control.Monad.Error
import Control.Monad.State
import Data.Char
import Data.List
import Data.Word
import System.IO

import Joy.Types

import Debug.Trace
}

%name parseSpecification Specification

%tokentype { Token }
%monad { Parse } { >>= } { return }
%lexer { lexerTakingContinuation } { EndOfInput }
%error { parseError }

%token
        sectionSeparator      { SectionSeparator }
        hereFile              { HereFile $$ }
        clientCode            { ClientCode $$ }
        languageLine          { LanguageLine _ _ }
        identifier            { Identifier $$ }
        string                { StringLiteral $$ }
        '|'                   { Bar }
        '::'                  { ColonColon }
        '('                   { LeftParenthesis }
        ')'                   { RightParenthesis }
        error_                { KeywordError }
        lexer                 { KeywordLexer }
        monad                 { KeywordMonad }
        monadic               { KeywordMonadic }
        name                  { KeywordName }
        names                 { KeywordNames }
        parser                { KeywordParser }
        partial               { KeywordPartial }
        token                 { KeywordToken }
        type                  { KeywordType }
        user                  { KeywordUser }
%%

Specification :: { Specification }
    : languageLine
      hereFile
      sectionSeparator
      DeclarationList
      sectionSeparator
      hereFile
    { case $1 of
        LanguageLine joyVersion clientLanguage
            -> Specification {
                 specificationJoyVersion = joyVersion,
                 specificationClientLanguage = clientLanguage,
                 specificationOutputHeader = ClientRaw $2,
                 specificationDeclarations = $4,
                 specificationOutputFooter = ClientRaw $6
               }
    }


DeclarationList :: { [Declaration] }
    :
    { [] }
    | DeclarationList monad clientCode
    { $1 ++ [MonadDeclaration $ ClientType $3] }
    | DeclarationList user lexer name clientCode
    { $1 ++ [UserLexerDeclaration (ClientExpression $5)] }
    | DeclarationList error_ clientCode
    { $1 ++ [ErrorDeclaration $ ClientExpression $3] }
    | DeclarationList lexer LexerDefinitionList
    { $1 ++ [LexerDeclaration Nothing $3] }
    | DeclarationList lexer name clientCode LexerDefinitionList
    { $1 ++ [LexerDeclaration (Just (ClientExpression $4)) $5] }
    | DeclarationList token type clientCode names TokenDefinitionList
    { $1 ++ [TokensDeclaration (ClientType $4) $6] }
    | DeclarationList NonterminalDeclaration
    { $1 ++ [$2] }


LexerDefinitionList :: { [(String, ClientExpression)] }
    :
    { [] }
    | LexerDefinitionList '|' string clientCode
    { $1 ++ [($3, ClientExpression $4)] }


TokenDefinitionList :: { [(GrammarSymbol, String)] }
    :
    { [] }
    | TokenDefinitionList '|' identifier clientCode
    { $1 ++ [(IdentifierTerminal $3, $4)] }
    | TokenDefinitionList '|' string clientCode
    { $1 ++ [(StringTerminal $3, $4)] }


NonterminalDeclaration :: { Declaration }
    : NonterminalDeclarationParserList identifier '::' clientCode
      NonterminalDeclarationRightHandSideList
    { NonterminalDeclaration {
        nonterminalDeclarationParsers = $1,
        nonterminalDeclarationGrammarSymbol = Nonterminal $2,
        nonterminalDeclarationType = ClientType $4,
        nonterminalDeclarationRightHandSides = $5
      } }

NonterminalDeclarationParserList :: { [(Bool, ClientExpression)] }
    :
    { [] }
    | NonterminalDeclarationParserList parser clientCode
    { $1 ++ [(False, ClientExpression $3)] }
    | NonterminalDeclarationParserList partial parser clientCode
    { $1 ++ [(True, ClientExpression $4)] }

NonterminalDeclarationRightHandSideList :: { [([GrammarSymbol], ClientAction)] }
    : NonterminalDeclarationRightHandSide
    { [$1] }
    | NonterminalDeclarationRightHandSideList NonterminalDeclarationRightHandSide
    { $1 ++ [$2] }

NonterminalDeclarationRightHandSide :: { ([GrammarSymbol], ClientAction) }
    : '|' IdentifierList clientCode
    { ($2, ClientAction False $3) }
    | '|' IdentifierList monadic clientCode
    { ($2, ClientAction True $4) }

IdentifierList :: { [GrammarSymbol] }
    :
    { [] }
    | IdentifierList identifier
    { $1 ++ [if isUpper $ head $2
              then Nonterminal $2
              else IdentifierTerminal $2] }
    | IdentifierList string
    { $1 ++ [StringTerminal $2] }

{


data ParseState = ParseState {
      parseStateInput :: String,
      parseStateLineNumber :: Word64,
      parseStateAtStartOfLine :: Bool,
      parseStateSectionNumber :: Int,
      parseStateLastWasHereFile :: Bool
    } deriving (Show)


type Parse = ErrorT SpecificationParseError (State ParseState)


data Token = EndOfInput
           | SectionSeparator
           | HereFile String
           | ClientCode String
           | LanguageLine JoyVersion ClientLanguage
           | Identifier String
           | StringLiteral String
           | Bar
           | ColonColon
           | LeftParenthesis
           | RightParenthesis
           | KeywordError
           | KeywordLexer
           | KeywordMonad
           | KeywordMonadic
           | KeywordName
           | KeywordNames
           | KeywordParser
           | KeywordPartial
           | KeywordToken
           | KeywordType
           | KeywordUser
instance Show Token where
    show EndOfInput = "<eof>"
    show SectionSeparator = "--"
    show (HereFile string) = "<here-file>"
    show (ClientCode string) = "{ " ++ string ++ "}"
    show (LanguageLine _ _) = "LANGUAGE"
    show (Identifier string) = string
    show (StringLiteral string) = "'" ++ (let t "" = ""
                                              t ('\'':rest) = "''" ++ t rest
                                              t (c:rest) = [c] ++ t rest
                                          in t string) ++ "'"
    show Bar = "'|'"
    show ColonColon = "'::'"
    show LeftParenthesis = "'('"
    show RightParenthesis = "')'"
    show KeywordError = "ERROR"
    show KeywordLexer = "LEXER"
    show KeywordMonad = "MONAD"
    show KeywordMonadic = "MONADIC"
    show KeywordName = "NAME"
    show KeywordNames = "NAMES"
    show KeywordParser = "PARSER"
    show KeywordPartial = "PARTIAL"
    show KeywordToken = "TOKEN"
    show KeywordType = "TYPE"
    show KeywordUser = "USER"

readSpecificationFile :: FilePath -> IO (Either SpecificationParseError Specification)
readSpecificationFile filename = do
  withFile filename ReadMode
           (\file -> do
              input <- hGetContents file >>= (\s -> length s `seq` return s)
              let initialState = ParseState {
                                   parseStateInput = input,
                                   parseStateLineNumber = 1,
                                   parseStateAtStartOfLine = True,
                                   parseStateSectionNumber = 0,
                                   parseStateLastWasHereFile = False
                                 }
              return $ evalState (runErrorT parseSpecification) initialState)


parseError :: Token -> Parse a
parseError token
    = throwParseError
      $ "Parsing error near " ++ (show token) ++ "."


throwParseError :: String -> Parse a
throwParseError message = do
  state <- getParseState
  let lineNumber = parseStateLineNumber state
      error = SpecificationParseError {
                specificationParseErrorMessage = message,
                specificationParseErrorLineNumber = lineNumber
              }
  throwError error


getParseState :: Parse ParseState
getParseState = lift get


putParseState :: ParseState -> Parse ()
putParseState state = lift $ put state


lexerTakingContinuation
    :: (Token -> Parse a) -> Parse a
lexerTakingContinuation continuation = do
  token <- lexerWrapper
  continuation token


lexerWrapper :: Parse Token
lexerWrapper = do
  state <- getParseState
  let input = parseStateInput state
      lastWasHereFile = parseStateLastWasHereFile state
      lineNumber = parseStateLineNumber state
      sectionNumber = parseStateSectionNumber state
  (token, rest) <- case (lastWasHereFile, lineNumber, sectionNumber) of
                     (True, _, _) -> lexer input
                     (_, 1, _) -> languageLineLexer input
                     (_, _, 0) -> hereFileLexer input
                     (_, _, n) | n < 2 -> lexer input
                     (_, _, _) -> hereFileLexer input
  state <- getParseState
  putParseState $ state {
                      parseStateInput = rest,
                      parseStateLastWasHereFile = case token of
                                                    HereFile _ -> True
                                                    _ -> False
                    }
  return token


lexer :: String -> Parse (Token, String)
lexer "" = return (EndOfInput, "")
lexer all@('-':'-':'\n':rest) = do
  processNewline
  state <- getParseState
  let atStartOfLine = parseStateAtStartOfLine state
  if atStartOfLine
    then do
      let sectionNumber = parseStateSectionNumber state
      putParseState $ state {
                             parseStateAtStartOfLine = False,
                             parseStateSectionNumber = sectionNumber + 1
                           }
      return (SectionSeparator, rest)
    else throwParseError $ "Unexpected character '-'."
lexer ('\n':rest) = do
  processNewline
  lexer rest
lexer all@('\'':_) = do
  processNonNewline
  (string, rest) <- readStringLiteral all
  return (StringLiteral string, rest)
lexer all@('"':_) = do
  processNonNewline
  (string, rest) <- readStringLiteral all
  return (StringLiteral string, rest)
lexer all@('{':_) = do
  processNonNewline
  (code, rest) <- readClientCode all
  return (ClientCode code, rest)
lexer ('|':rest) = do
  processNonNewline
  return (Bar, rest)
lexer (':':':':rest) = do
  processNonNewline
  return (ColonColon, rest)
lexer ('(':rest) = do
  processNonNewline
  return (LeftParenthesis, rest)
lexer (')':rest) = do
  processNonNewline
  return (RightParenthesis, rest)
lexer all@(c:rest) = do
  processNonNewline
  if isSpace c
    then lexer rest
    else if isAlpha c
      then do
        (identifier, rest) <- readIdentifier all
        let token = case identifier of
                      _ | identifier == "ERROR" -> KeywordError
                        | identifier == "LEXER" -> KeywordLexer
                        | identifier == "MONAD" -> KeywordMonad
                        | identifier == "MONADIC" -> KeywordMonadic
                        | identifier == "NAME" -> KeywordName
                        | identifier == "NAMES" -> KeywordNames
                        | identifier == "PARSER" -> KeywordParser
                        | identifier == "PARTIAL" -> KeywordPartial
                        | identifier == "TOKEN" -> KeywordToken
                        | identifier == "TYPE" -> KeywordType
                        | identifier == "USER" -> KeywordUser
                        | otherwise -> Identifier identifier
        return (token, rest)
      else do
        state <- getParseState
        let lineNumber = parseStateLineNumber state
        throwParseError
          $ "Unexpected character " ++ (show c) ++ " on line " ++ (show lineNumber)
            ++ "."


languageLineLexer :: String -> Parse (Token, String)
languageLineLexer input = do
  let (line, rest) = maybe ("", input)
                           (\point -> (take point input, drop (point + 1) input))
                           $ elemIndex '\n' input
      lineWords = words line
  state <- getParseState
  let lineNumber = parseStateLineNumber state
  putParseState $ state { parseStateLineNumber = lineNumber + 1 }
  case lineWords of
    ["LANGUAGE", "Joy/1.0", "Haskell"]
        -> return (LanguageLine JoyVersion1 Haskell, rest)
    ["LANGUAGE", "Joy/1.0", clientLanguage]
        -> throwParseError $ "Unknown client language " ++ clientLanguage ++ "."
    ["LANGUAGE", joyVersion, _]
        -> throwParseError $ "Unknown Joy version " ++ joyVersion ++ "."
    _ -> throwParseError $ "Invalid or missing LANGUAGE line." ++ show input

hereFileLexer :: String -> Parse (Token, String)
hereFileLexer "" = return (EndOfInput, "")
hereFileLexer input = do
  let lex' "" = return ("", "")
      lex' all@('-':'-':'\n':_) = return ("", all)
      lex' ('\n':rest) = do
        processNewline
        (result, rest) <- lex' rest
        return ("\n" ++ result, rest)
      lex' (c:rest) = do
        (result, rest) <- lex' rest
        return ([c] ++ result, rest)
  (result, rest) <- lex' input
  state <- getParseState
  putParseState $ state { parseStateLastWasHereFile = True }
  return (HereFile result, rest)


readIdentifier :: String -> Parse (String, String)
readIdentifier input = do
  return (takeWhile isAlpha input, dropWhile isAlpha input)


readStringLiteral :: String -> Parse (String, String)
readStringLiteral input = do
  let delimiter = head input
      lex' "" = throwParseError $ "Unexpected end of input in string literal."
      lex' (c:d:rest) | (c == d) && (c == delimiter) = do
                            (result, rest) <- lex' rest
                            return ([c] ++ result, rest)
      lex' (c:rest) | c == delimiter = return ("", rest)
                    | otherwise = do
                            (result, rest) <- lex' rest
                            return ([c] ++ result, rest)
  lex' $ tail input


readClientCode :: String -> Parse (String, String)
readClientCode input = do
  let lex' depth ('{':rest) | depth == 0 = lex' (depth+1) rest
                            | otherwise = do
                                (result, rest) <- lex' (depth+1) rest
                                return ("{" ++ result, rest)
      lex' depth ('}':rest) | depth == 1 = return ("", rest)
                            | otherwise = do
                                (result, rest) <- lex' (depth-1) rest
                                return ("}" ++ result, rest)
      lex' depth ('\n':rest) = do
                                 processNewline
                                 (result, rest) <- lex' depth rest
                                 return ("\n" ++ result, rest)
      lex' depth (c:rest) = do
                              (result, rest) <- lex' depth rest
                              return ([c] ++ result, rest)
      lex' depth "" = throwParseError $ "Unexpected end of input in client code."
  lex' 0 input


processNewline :: Parse ()
processNewline = do
  state <- getParseState
  let lineNumber = parseStateLineNumber state
  putParseState $ state {
                      parseStateLineNumber = lineNumber + 1,
                      parseStateAtStartOfLine = True
                    }


processNonNewline :: Parse ()
processNonNewline = do
  state <- getParseState
  putParseState $ state { parseStateAtStartOfLine = False }

}
