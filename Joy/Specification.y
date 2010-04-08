{
module Joy.Specification (
                          Specification(..),
                          JoyVersion(..),
                          ClientLanguage(..),
                          Declaration(..),
                          LexerDefinitionItem(..),
                          GrammarSymbol(..),
                          SpecificationParseError(..),
                          readSpecificationFile
                         )
    where

import Control.Monad.Error
import Control.Monad.State
import Data.Char
import Data.List
import Data.Word
import System.IO

import Joy.Client
import Joy.Documentation
}

%name parseSpecification Specification

%tokentype { Token }
%monad { Parse } { >>= } { return }
%lexer { lexerTakingContinuation } { EndOfInput _ }
%error { parseError }

%token
        sectionSeparator      { SectionSeparator _ }
        hereFile              { HereFile _ _ }
        clientCode            { ClientCode _ _ }
        languageLine          { LanguageLine _ _ _ }
        identifier            { Identifier _ _ }
        string                { StringLiteral _ _ }
        '|'                   { Bar _ }
        '::'                  { ColonColon _ }
        '('                   { LeftParenthesis _ }
        ')'                   { RightParenthesis _ }
        binary                { KeywordBinary _ }
        error_                { KeywordError _ }
        initial               { KeywordInitial _ }
        lexer                 { KeywordLexer _ }
        monad                 { KeywordMonad _ }
        monadic               { KeywordMonadic _ }
        name                  { KeywordName _ }
        names                 { KeywordNames _ }
        parent                { KeywordParent _ }
        parser                { KeywordParser _ }
        partial               { KeywordPartial _ }
        subexpression         { KeywordSubexpression _ }
        token                 { KeywordToken _ }
        type                  { KeywordType _ }
        user                  { KeywordUser _ }
%%

Specification :: { Specification }
    : languageLine
      hereFile
      sectionSeparator
      DeclarationList
      sectionSeparator
      hereFile
    { case ($1, $2, $6) of
        (LanguageLine _ joyVersion clientLanguage, HereFile _ header, HereFile _ footer)
            -> Specification {
                 specificationJoyVersion = joyVersion,
                 specificationClientLanguage = clientLanguage,
                 specificationOutputHeader = ClientRaw header,
                 specificationDeclarations = $4,
                 specificationOutputFooter = ClientRaw footer
               }
    }


DeclarationList :: { [Declaration] }
    :
    { [] }
    
    | DeclarationList monad clientCode
    { case ($2, $3) of
        (KeywordMonad lineNumber, ClientCode _ body)
          -> $1 ++ [MonadDeclaration lineNumber $ ClientType body] }
    
    | DeclarationList user MaybeInitial lexer name identifier
    { case ($2, $3, $6) of
        (KeywordUser lineNumber, (_, maybeInitial), Identifier _ name)
          -> $1 ++ [UserLexerDeclaration lineNumber
                                         maybeInitial
                                         name] }
    
    | DeclarationList error_ clientCode
    { case ($2, $3) of
        (KeywordError lineNumber, ClientCode _ body)
          -> $1 ++ [ErrorDeclaration lineNumber $ ClientExpression body] }
    
    | DeclarationList MaybeInitial MaybeBinary lexer MaybeName MaybeParent
      LexerDefinitionList
    { case ($2, $3, $4) of
        ((Nothing, maybeInitial), (Nothing, maybeBinary), KeywordLexer lineNumber)
          -> $1 ++ [LexerDeclaration lineNumber maybeInitial maybeBinary $5 $6 $7]
        ((Nothing, maybeInitial), (Just lineNumber, maybeBinary), _)
          -> $1 ++ [LexerDeclaration lineNumber maybeInitial maybeBinary $5 $6 $7]
        ((Just lineNumber, maybeInitial), (_, maybeBinary), _)
          -> $1 ++ [LexerDeclaration lineNumber maybeInitial maybeBinary $5 $6 $7] }
    
    | DeclarationList token type clientCode
    { case ($2, $4) of
        (KeywordToken lineNumber, ClientCode _ body)
          -> $1 ++ [TokensDeclaration lineNumber (ClientType body) []] }
    | DeclarationList token type clientCode names TokenDefinitionList
    {% do
	case ($6) of
          [] -> throwParseError $ "TOKENS declaration gives NAMES but no items."
          _ -> return ()
	return $ case ($2, $4) of
         (KeywordToken lineNumber, ClientCode _ body)
           -> $1 ++ [TokensDeclaration lineNumber (ClientType body) $6] }
    
    | DeclarationList NonterminalDeclaration
    { $1 ++ [$2] }


MaybeInitial :: { (Maybe LineNumber, Bool) }
    :
    { (Nothing, False) }
    | initial
    { case $1 of
        KeywordInitial lineNumber -> (Just lineNumber, True) }


MaybeBinary :: { (Maybe LineNumber, Bool) }
    :
    { (Nothing, False) }
    | binary
    { case $1 of
        (KeywordBinary lineNumber) -> (Just lineNumber, True) }


MaybeName :: { Maybe String }
    :
    { Nothing }
    | name identifier
    { case $2 of
        (Identifier _ name) -> Just name }


MaybeParent :: { Maybe String }
    :
    { Nothing }
    | parent identifier
    { case $2 of
        (Identifier _ name) -> Just name }


LexerDefinitionList :: { [LexerDefinitionItem] }
    :
    { [] }
    | LexerDefinitionList '|' string clientCode
    { case ($3, $4) of
        (StringLiteral lineNumber string, ClientCode _ body)
          -> $1 ++ [LexerNormalItem lineNumber string (ClientExpression body)] }
    | LexerDefinitionList '|' subexpression identifier string
    { case ($3, $4, $5) of
        (KeywordSubexpression lineNumber, Identifier _ name, StringLiteral _ value)
            -> $1 ++ [LexerSubexpressionItem lineNumber name value Nothing] }
    | LexerDefinitionList '|' subexpression identifier string clientCode
    { case ($3, $4, $5, $6) of
        (KeywordSubexpression lineNumber, Identifier _ name, StringLiteral _ value,
         ClientCode _ body)
            -> $1 ++ [LexerSubexpressionItem lineNumber name value
                                             (Just $ ClientExpression body)] }


TokenDefinitionList :: { [(GrammarSymbol, String)] }
    :
    { [] }
    | TokenDefinitionList '|' identifier clientCode
    {% case ($3, $4) of
         (Identifier terminalLineNumber terminal, ClientCode _ body)
           -> if isLower $ head terminal
              then return $ $1 ++ [(IdentifierTerminal terminal, body)]
              else throwParseError
                       $ "Terminal must begin with a lowercase letter at line "
                         ++ (show terminalLineNumber) }
    | TokenDefinitionList '|' string clientCode
    { case ($3, $4) of
         (StringLiteral _ terminal, ClientCode _ body)
           -> $1 ++ [(StringTerminal terminal, body)] }


NonterminalDeclaration :: { Declaration }
    : NonterminalDeclarationParserList identifier '::' clientCode
      NonterminalDeclarationRightHandSideList
    {% case ($1, $2, $4) of
         ((Nothing, parsers),
          Identifier lineNumber@nameLineNumber name,
          ClientCode _ body)
           -> do
             if isUpper $ head name
               then return ()
               else throwParseError
                    $ "Nonterminal must begin with an uppercase letter at line "
                      ++ (show nameLineNumber)
             return $ NonterminalDeclaration {
                          nonterminalDeclarationLineNumber = lineNumber,
                          nonterminalDeclarationParsers = parsers,
                          nonterminalDeclarationGrammarSymbol = Nonterminal name,
                          nonterminalDeclarationType = ClientType body,
                          nonterminalDeclarationRightHandSides = $5
                        }
         ((Just lineNumber, parsers),
          Identifier nameLineNumber name,
          ClientCode _ body)
           -> do
             if isUpper $ head name
               then return ()
               else throwParseError
                    $ "Nonterminal must begin with an uppercase letter at line "
                      ++ (show nameLineNumber)
             return $ NonterminalDeclaration {
                          nonterminalDeclarationLineNumber = lineNumber,
                          nonterminalDeclarationParsers = parsers,
                          nonterminalDeclarationGrammarSymbol = Nonterminal name,
                          nonterminalDeclarationType = ClientType body,
                          nonterminalDeclarationRightHandSides = $5
                        }
    }

NonterminalDeclarationParserList :: { (Maybe LineNumber, [(Bool, ClientExpression)]) }
    :
    { (Nothing, []) }
    | NonterminalDeclarationParserList parser clientCode
    { case ($1, $2, $3) of
        ((Nothing, start), KeywordParser lineNumber, ClientCode _ body)
          -> (Just lineNumber, start ++ [(False, ClientExpression body)])
        ((Just lineNumber, start), _, ClientCode _ body)
          -> (Just lineNumber, start ++ [(False, ClientExpression body)]) }
    | NonterminalDeclarationParserList partial parser clientCode
    { case ($1, $2, $4) of
        ((Nothing, start), KeywordPartial lineNumber, ClientCode _ body)
          -> (Just lineNumber, start ++ [(True, ClientExpression body)])
        ((Just lineNumber, start), _, ClientCode _ body)
          -> (Just lineNumber, start ++ [(True, ClientExpression body)]) }

NonterminalDeclarationRightHandSideList :: { [([GrammarSymbol], ClientAction)] }
    : NonterminalDeclarationRightHandSide
    { [$1] }
    | NonterminalDeclarationRightHandSideList NonterminalDeclarationRightHandSide
    { $1 ++ [$2] }

NonterminalDeclarationRightHandSide :: { ([GrammarSymbol], ClientAction) }
    : '|' IdentifierList clientCode
    { case $3 of
        (ClientCode _ body)
          -> ($2, ClientAction False body) }
    | '|' IdentifierList monadic clientCode
    { case $4 of
        (ClientCode _ body)
          -> ($2, ClientAction True body) }

IdentifierList :: { [GrammarSymbol] }
    :
    { [] }
    | IdentifierList identifier
    { case $2 of
        (Identifier _ identifier)
          -> $1 ++ [if isUpper $ head identifier
                      then Nonterminal identifier
                      else IdentifierTerminal identifier] }
    | IdentifierList string
    { case $2 of
        (StringLiteral _ string)
          -> $1 ++ [StringTerminal string] }

{

data Specification = Specification {
      specificationJoyVersion :: JoyVersion,
      specificationClientLanguage :: ClientLanguage,
      specificationDeclarations :: [Declaration],
      specificationOutputHeader :: ClientRaw,
      specificationOutputFooter :: ClientRaw
    }


data JoyVersion = JoyVersion1


data ClientLanguage = Haskell


data Declaration = MonadDeclaration LineNumber ClientType
                 | ErrorDeclaration LineNumber ClientExpression
                 | UserLexerDeclaration LineNumber
                                        Bool
                                        String
                 | LexerDeclaration LineNumber
                                    Bool
                                    Bool
                                    (Maybe String)
                                    (Maybe String)
                                    [LexerDefinitionItem]
                 | TokensDeclaration LineNumber ClientType [(GrammarSymbol, String)]
                 | NonterminalDeclaration {
                     nonterminalDeclarationLineNumber
                         :: LineNumber,
                     nonterminalDeclarationGrammarSymbol
                         :: GrammarSymbol,
                     nonterminalDeclarationType
                         :: ClientType,
                     nonterminalDeclarationParsers
                         :: [(Bool, ClientExpression)],
                     nonterminalDeclarationRightHandSides
                         :: [([GrammarSymbol], ClientAction)]
                   }


instance Located Declaration where
    location (MonadDeclaration result _) = result
    location (ErrorDeclaration result _) = result
    location (UserLexerDeclaration result _ _) = result
    location (LexerDeclaration result _ _ _ _ _) = result
    location (TokensDeclaration result _ _) = result
    location result@(NonterminalDeclaration { })
        = nonterminalDeclarationLineNumber result


data LexerDefinitionItem
    = LexerNormalItem LineNumber String ClientExpression
    | LexerSubexpressionItem LineNumber String String (Maybe ClientExpression)


instance Located LexerDefinitionItem where
    location (LexerNormalItem result _ _) = result
    location (LexerSubexpressionItem result _ _ _) = result


data GrammarSymbol = IdentifierTerminal String
                   | StringTerminal String
                   | Nonterminal String
                     deriving (Eq)


data SpecificationParseError = SpecificationParseError {
      specificationParseErrorMessage :: String,
      specificationParseErrorLineNumber :: LineNumber
    }
instance Error SpecificationParseError where
    strMsg message = SpecificationParseError {
                            specificationParseErrorMessage = message,
                            specificationParseErrorLineNumber = 0
                          }
instance Show SpecificationParseError where
    show error
        = "Line "
          ++ (show $ specificationParseErrorLineNumber error)
          ++ " of grammar specification: "
          ++ (specificationParseErrorMessage error)


data ParseState = ParseState {
      parseStateInput :: String,
      parseStateLineNumber :: LineNumber,
      parseStateAtStartOfLine :: Bool,
      parseStateSectionNumber :: Int,
      parseStateLastWasHereFile :: Bool
    } deriving (Show)


type Parse = ErrorT SpecificationParseError (State ParseState)


data Token = EndOfInput LineNumber
           | SectionSeparator LineNumber
           | HereFile LineNumber String
           | ClientCode LineNumber String
           | LanguageLine LineNumber JoyVersion ClientLanguage
           | Identifier LineNumber String
           | StringLiteral LineNumber String
           | Bar LineNumber
           | ColonColon LineNumber
           | LeftParenthesis LineNumber
           | RightParenthesis LineNumber
           | KeywordBinary LineNumber
           | KeywordError LineNumber
           | KeywordInitial LineNumber
           | KeywordLexer LineNumber
           | KeywordMonad LineNumber
           | KeywordMonadic LineNumber
           | KeywordName LineNumber
           | KeywordNames LineNumber
           | KeywordParent LineNumber
           | KeywordParser LineNumber
           | KeywordPartial LineNumber
           | KeywordSubexpression LineNumber
           | KeywordToken LineNumber
           | KeywordType LineNumber
           | KeywordUser LineNumber
instance Located Token where
    location (EndOfInput result) = result
    location (SectionSeparator result) = result
    location (HereFile result _) = result
    location (ClientCode result _) = result
    location (LanguageLine result _ _) = result
    location (Identifier result _) = result
    location (StringLiteral result _) = result
    location (Bar result) = result
    location (ColonColon result) = result
    location (LeftParenthesis result) = result
    location (RightParenthesis result) = result
    location (KeywordBinary result) = result
    location (KeywordError result) = result
    location (KeywordInitial result) = result
    location (KeywordLexer result) = result
    location (KeywordMonad result) = result
    location (KeywordMonadic result) = result
    location (KeywordName result) = result
    location (KeywordNames result) = result
    location (KeywordParent result) = result
    location (KeywordParser result) = result
    location (KeywordPartial result) = result
    location (KeywordSubexpression result) = result
    location (KeywordToken result) = result
    location (KeywordType result) = result
    location (KeywordUser result) = result
instance Show Token where
    show (EndOfInput _) = "<eof>"
    show (SectionSeparator _) = "--"
    show (HereFile _ string) = "<here-file>"
    show (ClientCode _ string) = "{ " ++ string ++ "}"
    show (LanguageLine _ _ _) = "LANGUAGE"
    show (Identifier _ string) = string
    show (StringLiteral _ string) = "'" ++ (let t "" = ""
                                                t ('\'':rest) = "''" ++ t rest
                                                t (c:rest) = [c] ++ t rest
                                            in t string) ++ "'"
    show (Bar _) = "'|'"
    show (ColonColon _) = "'::'"
    show (LeftParenthesis _) = "'('"
    show (RightParenthesis _) = "')'"
    show (KeywordBinary _) = "BINARY"
    show (KeywordError _) = "ERROR"
    show (KeywordInitial _) = "INITIAL"
    show (KeywordLexer _) = "LEXER"
    show (KeywordMonad _) = "MONAD"
    show (KeywordMonadic _) = "MONADIC"
    show (KeywordName _) = "NAME"
    show (KeywordNames _) = "NAMES"
    show (KeywordParent _) = "PARENT"
    show (KeywordParser _) = "PARSER"
    show (KeywordPartial _) = "PARTIAL"
    show (KeywordSubexpression _) = "SUBEXPRESSION"
    show (KeywordToken _) = "TOKEN"
    show (KeywordType _) = "TYPE"
    show (KeywordUser _) = "USER"

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
                                                    HereFile _ _ -> True
                                                    _ -> False
                    }
  return token


lexer :: String -> Parse (Token, String)
lexer "" = do
  lineNumber <- getLineNumber
  return (EndOfInput lineNumber, "")
lexer all@('-':'-':'\n':rest) = do
  lineNumber <- getLineNumber
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
      return (SectionSeparator lineNumber, rest)
    else throwParseError $ "Unexpected character '-'."
lexer ('\n':rest) = do
  processNewline
  lexer rest
lexer all@('\'':_) = do
  lineNumber <- getLineNumber
  processNonNewline
  (string, rest) <- readStringLiteral all
  return (StringLiteral lineNumber string, rest)
lexer all@('"':_) = do
  lineNumber <- getLineNumber
  processNonNewline
  (string, rest) <- readStringLiteral all
  return (StringLiteral lineNumber string, rest)
lexer ('{':'-':rest) = do
  rest <- skipBalancedComments rest
  lexer rest
lexer all@('{':_) = do
  lineNumber <- getLineNumber
  processNonNewline
  (code, rest) <- readClientCode all
  return (ClientCode lineNumber code, rest)
lexer ('-':'}':rest) = do
  lineNumber <- getLineNumber
  throwParseError $ "Unbalanced '-}'."
lexer ('|':rest) = do
  lineNumber <- getLineNumber
  processNonNewline
  return (Bar lineNumber, rest)
lexer (':':':':rest) = do
  lineNumber <- getLineNumber
  processNonNewline
  return (ColonColon lineNumber, rest)
lexer ('(':rest) = do
  lineNumber <- getLineNumber
  processNonNewline
  return (LeftParenthesis lineNumber, rest)
lexer (')':rest) = do
  lineNumber <- getLineNumber
  processNonNewline
  return (RightParenthesis lineNumber, rest)
lexer all@(c:rest) = do
  lineNumber <- getLineNumber
  processNonNewline
  if isSpace c
    then lexer rest
    else if isAlpha c
      then do
        (identifier, rest) <- readIdentifier all
        let token = case identifier of
                      _ | identifier == "BINARY" -> KeywordBinary lineNumber
                        | identifier == "ERROR" -> KeywordError lineNumber
                        | identifier == "INITIAL" -> KeywordInitial lineNumber
                        | identifier == "LEXER" -> KeywordLexer lineNumber
                        | identifier == "MONAD" -> KeywordMonad lineNumber
                        | identifier == "MONADIC" -> KeywordMonadic lineNumber
                        | identifier == "NAME" -> KeywordName lineNumber
                        | identifier == "NAMES" -> KeywordNames lineNumber
                        | identifier == "PARENT" -> KeywordParent lineNumber
                        | identifier == "PARSER" -> KeywordParser lineNumber
                        | identifier == "PARTIAL" -> KeywordPartial lineNumber
                        | identifier == "SUBEXPRESSION"
                            -> KeywordSubexpression lineNumber
                        | identifier == "TOKEN" -> KeywordToken lineNumber
                        | identifier == "TYPE" -> KeywordType lineNumber
                        | identifier == "USER" -> KeywordUser lineNumber
                        | otherwise -> Identifier lineNumber identifier
        return (token, rest)
      else throwParseError
             $ "Unexpected character " ++ (show c)
               ++ " on line " ++ (show lineNumber)
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
        -> return (LanguageLine lineNumber JoyVersion1 Haskell, rest)
    ["LANGUAGE", "Joy/1.0", clientLanguage]
        -> throwParseError $ "Unknown client language " ++ clientLanguage ++ "."
    ["LANGUAGE", joyVersion, _]
        -> throwParseError $ "Unknown Joy version " ++ joyVersion ++ "."
    _ -> throwParseError $ "Invalid or missing LANGUAGE line." ++ show input

hereFileLexer :: String -> Parse (Token, String)
hereFileLexer "" = do
  lineNumber <- getLineNumber
  return (EndOfInput lineNumber, "")
hereFileLexer input = do
  lineNumber <- getLineNumber
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
  return (HereFile lineNumber result, rest)


readIdentifier :: String -> Parse (String, String)
readIdentifier input = do
  return (takeWhile isAlpha input, dropWhile isAlpha input)


readStringLiteral :: String -> Parse (String, String)
readStringLiteral input = do
  let delimiter = head input
      lex' "" = throwParseError $ "Unexpected end of input in string literal."
      lex' "\n" = throwParseError $ "Unexpected newline in string literal."
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


skipBalancedComments :: String -> Parse String
skipBalancedComments input = do
  startLineNumber <- getLineNumber
  let skipBalancedComments' input =
          case input of
            ('{':'-':rest) -> do
                                processNonNewline
                                rest <- skipBalancedComments' rest
                                skipBalancedComments' rest
            ('-':'}':rest) -> do
                                processNonNewline
                                return $ rest
            ('\n':rest) -> do
                                processNewline
                                skipBalancedComments' rest
            (c:rest) -> do
                                processNonNewline
                                skipBalancedComments' rest
            "" -> do
                                throwParseError
                                  $ "Unbalanced '{-' on line " ++ (show startLineNumber)
  skipBalancedComments' input


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


getLineNumber :: Parse LineNumber
getLineNumber = do
  state <- getParseState
  return $ parseStateLineNumber state

}
