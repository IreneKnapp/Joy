module Joy.Types (
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
                 )
    where

import Control.Monad.Error
import Data.Word


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


data Declaration = MonadDeclaration ClientType
                 | ErrorDeclaration ClientExpression
                 | UserLexerDeclaration ClientExpression
                 | LexerDeclaration (Maybe ClientExpression)
                                    [(String, ClientExpression)]
                 | TokensDeclaration ClientType [(GrammarSymbol, String)]
                 | NonterminalDeclaration {
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
