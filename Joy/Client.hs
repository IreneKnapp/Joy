module Joy.Client (
                   ClientRaw(..),
                   ClientType(..),
                   ClientExpression(..),
                   ClientAction(..)
                  )
    where


data ClientRaw = ClientRaw String


data ClientType = ClientType String


data ClientExpression = ClientExpression String


data ClientAction = ClientAction Bool String
