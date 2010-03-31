module Joy.Types (
                  LineNumber(..),
                  Located(..),
                  Specification(..),
                  JoyVersion(..),
                  ClientLanguage(..),
                  Declaration(..),
                  GrammarSymbol(..),
                  ClientRaw(..),
                  ClientType(..),
                  ClientExpression(..),
                  ClientAction(..),
                  SpecificationParseError(..),
                  Generation(..),
                  GenerationError(..),
                  GenerationState(..),
                  LexerInformation(..),
                 )
    where

import Control.Monad.Error
import Control.Monad.State
import Data.Word


type LineNumber = Word64


class Located a where
    location :: a -> LineNumber


data Specification = Specification {
      specificationJoyVersion :: JoyVersion,
      specificationClientLanguage :: ClientLanguage,
      specificationDeclarations :: [Declaration],
      specificationOutputHeader :: ClientRaw,
      specificationOutputFooter :: ClientRaw
    } deriving (Show)


data JoyVersion = JoyVersion1
                  deriving (Show)


data ClientLanguage = Haskell
                      deriving (Show)


data Declaration = MonadDeclaration LineNumber ClientType
                 | ErrorDeclaration LineNumber ClientExpression
                 | UserLexerDeclaration LineNumber Bool ClientExpression
                 | LexerDeclaration LineNumber
                                    Bool
                                    (Maybe ClientExpression)
                                    [(String, ClientExpression)]
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
                   deriving (Show)


instance Located Declaration where
    location (MonadDeclaration result _) = result
    location (ErrorDeclaration result _) = result
    location (UserLexerDeclaration result _ _) = result
    location (LexerDeclaration result _ _ _) = result
    location (TokensDeclaration result _ _) = result
    location result@(NonterminalDeclaration { })
        = nonterminalDeclarationLineNumber result


data GrammarSymbol = IdentifierTerminal String
                   | StringTerminal String
                   | Nonterminal String
                     deriving (Eq, Show)


data ClientRaw = ClientRaw String
                 deriving (Show)


data ClientType = ClientType String
                  deriving (Show)


data ClientExpression = ClientExpression String
                        deriving (Show)


data ClientAction = ClientAction Bool String
                    deriving (Show)


data SpecificationParseError = SpecificationParseError {
      specificationParseErrorMessage :: String,
      specificationParseErrorLineNumber :: Word64
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


type Generation = ErrorT GenerationError (StateT GenerationState IO)


data GenerationError = GenerationError String
instance Error GenerationError where
    strMsg message = GenerationError message
instance Show GenerationError where
    show (GenerationError string) = string


data GenerationState = GenerationState {
        generationStateSpecification :: Specification,
        generationStateMaybeMonadType :: Maybe ClientType,
        generationStateMaybeLexerInformation :: Maybe LexerInformation,
        generationStateMaybeErrorFunction :: Maybe ClientExpression,
        generationStateTerminals :: [GrammarSymbol],
        generationStateNonterminals :: [GrammarSymbol],
        generationStateProductions
            :: [(GrammarSymbol, [GrammarSymbol], ClientExpression)]
      } deriving (Show)


data LexerInformation = LexerInformation {
        lexerInformationInitialName :: ClientExpression,
        lexerInformationInitialDeclaration :: Declaration,
        lexerInformationUserDeclarations :: [Declaration],
        lexerInformationNonuserDeclarations :: [Declaration]
    } deriving (Show)
