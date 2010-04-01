module Joy.Types (
                  LineNumber(..),
                  UniqueID(..),
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
                  EnumSet,
                  DFA(..),
                  DFAState(..),
                  NFA(..),
                  NFAState(..),
                  Generation(..),
                  GenerationError(..),
                  GenerationState(..),
                  LexerInformation(..),
                 )
    where

import Control.Monad.Error
import Control.Monad.State
import Data.Map (Map)
import Data.Set (Set)
import Data.Word

import Joy.EnumSets


type LineNumber = Word64


type UniqueID = Word64


class Located a where
    location :: a -> LineNumber


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
                     deriving (Eq)


data ClientRaw = ClientRaw String


data ClientType = ClientType String


data ClientExpression = ClientExpression String


data ClientAction = ClientAction Bool String


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


data DFA input data' = DFA (Map UniqueID (DFAState input data'))
                           (DFAState input data')


data DFAState input data' = DFAState {
      dfaStateID :: UniqueID,
      dfaStateAccepting :: Bool,
      dfaStateSuccessors :: Map input UniqueID,
      dfaStateData :: data'
    }


data NFA input data' = NFA (Map UniqueID (NFAState input data'))
                           (Set (NFAState input data'))


data NFAState input data' = NFAState {
      nfaStateID :: UniqueID,
      nfaStateAccepting :: Bool,
      nfaStateSuccessors :: Map input (Set UniqueID),
      nfaStateData :: data'
    }


type Generation = ErrorT GenerationError (StateT GenerationState IO)


data GenerationError = GenerationError String
instance Error GenerationError where
    strMsg message = GenerationError message
instance Show GenerationError where
    show (GenerationError string) = string


data GenerationState = GenerationState {
        generationStateUniqueIDCounter :: UniqueID,
        generationStateSpecification :: Specification,
        generationStateMaybeMonadType :: Maybe ClientType,
        generationStateMaybeLexerInformation :: Maybe LexerInformation,
        generationStateCompiledLexers :: [(String, DFA Char ())],
        generationStateMaybeErrorFunction :: Maybe ClientExpression,
        generationStateTerminals :: [GrammarSymbol],
        generationStateNonterminals :: [GrammarSymbol],
        generationStateProductions
            :: [(GrammarSymbol, [GrammarSymbol], ClientExpression)]
      }


data LexerInformation = LexerInformation {
        lexerInformationMaybeInitialName :: Maybe ClientExpression,
        lexerInformationUserNames :: [ClientExpression],
        lexerInformationNonuserNamesAndDefinitions
            :: [(ClientExpression, [(String, ClientExpression)])]
    }
