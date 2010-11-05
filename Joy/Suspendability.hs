{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances,
             UndecidableInstances, TypeSynonymInstances #-}
module Joy.Suspendability (
                           SuspendableMonad(..),
                           throw,
                           catch,
                           block,
                           unblock,
                           bracket,
                           finally,
                           onException,
                           withFile
                          )
  where

import qualified Control.Exception as Ex
import Control.Monad.Trans
import Control.Monad.Error (Error, ErrorT)
import qualified Control.Monad.Error as E
import Control.Monad.State (State, StateT)
import qualified Control.Monad.State as S
import Prelude hiding (catch)
import qualified System.IO as IO


class (Monad m) => StateLikeSuspendableMonad m state where
  get :: m state
  put :: state -> m ()
class (Monad m) => ErrorLikeSuspendableMonad m error where
  throwError :: error -> m a
class (StateLikeSuspendableMonad m state, ErrorLikeSuspendableMonad m error)
  => SuspendableMonad m state error result
  | m -> state,
    m -> error
  where
    resume :: state -> (m result) -> IO (Either error (result, state))


instance StateLikeSuspendableMonad IO () where
  get = return ()
  put () = return ()
instance ErrorLikeSuspendableMonad IO error where
  throwError error = undefined
instance SuspendableMonad IO () error result where
  resume () action = do
    result <- action
    return $ Right (result, ())


instance (StateLikeSuspendableMonad m substate)
  => StateLikeSuspendableMonad (StateT state m) (state, substate) where
    get = do
      state <- S.get
      substate <- lift get
      return (state, substate)
    put (state, substate) = do
      S.put state
      lift $ put substate
instance (ErrorLikeSuspendableMonad m error)
  => ErrorLikeSuspendableMonad (StateT state m) error where
    throwError error = lift $ throwError error
instance (SuspendableMonad m substate error (result, state))
  => SuspendableMonad (StateT state m) (state, substate) error result where
    resume (state, substate) action = do
      either <- resume substate $ S.evalStateT (do
                                                 result <- action
                                                 state <- S.get
                                                 return (result, state))
                                               state
      case either of
        Left error -> return $ Left error
        Right ((result, state), substate)
          -> return $ Right (result, (state, substate))


instance (StateLikeSuspendableMonad m substate, Error error)
  => StateLikeSuspendableMonad (ErrorT error m) substate where
    get = lift get
    put substate =
      lift $ put substate
instance (ErrorLikeSuspendableMonad m error, Error error)
  => ErrorLikeSuspendableMonad (ErrorT error m) error where
    throwError error = E.throwError error
instance (SuspendableMonad m substate error (Either error result),
          Error error)
  => SuspendableMonad (ErrorT error m) substate error result where
    resume substate action = do
      either <- resume substate $ E.runErrorT action
      case either of
        Left error -> return $ Left error
        Right (Left error, substate) -> return $ Left error
        Right (Right result, substate) -> return $ Right (result, substate)


throw :: (MonadIO m, Ex.Exception exception) => exception -> m a
throw exception = liftIO $ Ex.throwIO exception


catch :: (SuspendableMonad m state error result,
          MonadIO m,
          Ex.Exception exception)
      => m result -> (exception -> m result) -> m result
catch action handler = do
  state <- get
  either <- liftIO $ Ex.catch (resume state action)
                              (\exception -> resume state $ handler exception)
  case either of
    Left error -> throwError error
    Right (result, state) -> do
      put state
      return result


block :: (SuspendableMonad m state error result, MonadIO m)
      => (m result) -> m result
block action = do
  state <- get
  either <- liftIO $ Ex.block $ resume state action
  case either of
    Left error -> throwError error
    Right (result, state) -> do
      put state
      return result


unblock :: (SuspendableMonad m state error result, MonadIO m)
        => (m result) -> m result
unblock action = do
  state <- get
  either <- liftIO $ Ex.unblock $ resume state action
  case either of
    Left error -> throwError error
    Right (result, state) -> do
      put state
      return result


bracket :: (SuspendableMonad m state error resource,
            SuspendableMonad m state error result,
            SuspendableMonad m state error ignored,
            MonadIO m)
        => (m resource)
        -> (resource -> m ignored)
        -> (resource -> m result)
        -> m result
bracket before after action = do
  block $ do
    resource <- before
    result <- unblock (action resource) `onException` (after resource)
    _ <- after resource
    return result


finally :: (SuspendableMonad m state error result, MonadIO m)
        => (m result) -> (m ignored) -> m result
finally action after = do
  block $ do
    result <- unblock action `onException` after
    _ <- after
    return result


onException :: (SuspendableMonad m state error result, MonadIO m)
            => (m result) -> (m ignored) -> m result
onException action handler = do
  catch action
        (\exception -> do
           _ <- handler
           Ex.throw (exception :: Ex.SomeException))


withFile :: (SuspendableMonad m state error result, MonadIO m)
         => IO.FilePath -> IO.IOMode -> (IO.Handle -> m result) -> m result
withFile path mode action = do
  state <- get
  either <- liftIO $ IO.withFile path mode
                                 (\handle -> resume state $ action handle)
  case either of
    Left error -> throwError error
    Right (result, state) -> do
      put state
      return result
