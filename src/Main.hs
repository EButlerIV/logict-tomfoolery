{-# LANGUAGE FunctionalDependencies ,  MultiParamTypeClasses,
             FlexibleInstances, FlexibleContexts, UndecidableInstances,
             ScopedTypeVariables #-}


module Main where

import Control.Monad.Logic
import Control.Monad.Logic.Class
import Data.Witherable


import Data.List (delete, (\\))
import Control.Lens (element, (.~))
import Control.Applicative ((<|>) )
import Control.Monad.Trans.State.Strict as State
import Control.Monad.Trans.State.Strict as StrictST
import Control.Monad.Identity
import Control.Monad.Trans.Class
-- import Data.Foldable (asum)
-- import Data.Sequence as Seq
import Data.Set as Set
import Control.Applicative as CA
import qualified Data.Map as Map
import Data.Maybe (listToMaybe)
import qualified Control.Monad.State.Class as STC
import Control.Monad.State.Class (MonadState)

type GridM a = SetT Position (LogicT (State [Position])) a

type Graph = Map.Map Position Label

data Position = Position !Integer !Integer
  deriving (Ord, Eq, Show)

data Label = Start | End | Other
  deriving (Ord, Eq, Show, Read)

instance MonadTrans (SetT e) where
  lift m = SetT $ lift m

instance MonadState s m => MonadState s (SetT e m) where
  put e = lift $ STC.put e
  get = lift STC.get

instance MonadPlus m => MonadPlus (SetT e m) where
  mzero = SetT $ mzero
  mplus (SetT ma) (SetT mb) = SetT $ mplus ma mb

instance (MonadPlus m, Alternative m) => Alternative (SetT e m) where
  empty = SetT $ CA.empty
  (SetT ma ) <|> (SetT mb) = SetT $ ma <|> mb


board :: Map.Map Position Label
board = fmap (\x -> case x of 'S' -> Start; 'E' -> End; '0' -> Other) $ Map.fromList [
    (Position 0 0, 'S'), (Position 0 1, '0'), (Position 0 2, '0'),
    (Position 1 0, '0'), (Position 1 1, '0'), (Position 1 2, '0'),
    (Position 2 0, '0'), (Position 2 1, '0'), (Position 2 2, '0'),
    (Position 3 0, '0'), (Position 3 1, '0'), (Position 3 2, 'E'),
    (Position 4 0, '0'), (Position 4 1, 'E'), (Position 4 2, '0')
  ]

newtype SetT e m a = SetT (StateT (Set e) m a)

unsetT :: SetT e m a -> (StateT (Set e) m a)
unsetT (SetT m) = m

instance (Functor m) => Functor (SetT e m) where
    fmap f (SetT sm) = SetT $ fmap f sm

-- if StateT had a better applicative, maybe we could just do Applicative  m =>
instance (Monad m) => Applicative (SetT e m) where
  pure a = SetT $ pure a
  fm <*> (SetT ma) =   SetT $ (unsetT fm) <*> ma

instance Monad m => Monad (SetT e m) where
  return = SetT . return
  ma >>= f = SetT $ (unsetT ma >>= (unsetT . f ))

class (Monad m , Ord e) => MonadSet m e | m -> e where
  isMember :: e -> m Bool
  addMember :: e -> m ()

instance  (Monad m , Ord e) => MonadSet (SetT e m) e where
  isMember = isMemberSetT
  addMember = addMemberSetT

isMemberSetT :: (Ord e, Monad m) => e -> SetT e m Bool
isMemberSetT el = SetT $ do
  s <- get
  return $ member el s

addMemberSetT :: (Ord e, Monad m) => e -> SetT e m ()
addMemberSetT el = SetT $ do
  s <- get
  State.put $ insert el s
  return ()

push :: MonadState [e] m => e -> m ()
push el = do
  ls <- STC.get
  STC.put $ el: ls

getStack :: MonadState [e] m => m [e]
getStack = STC.get

instance (MonadPlus m,MonadLogic m) => MonadLogic (SetT e m) where
      msplit (SetT sm) =

          SetT $  StrictST.StateT $ \s ->
                      do r <- msplit (StrictST.runStateT sm s)
                         case r of
                              Nothing          -> return (Nothing, s)
                              Just ((a,s'), m) ->
                                  return (Just (a, SetT $ StrictST.StateT (\_ -> m)), s')

      interleave (SetT ma) (SetT mb) = SetT $ StrictST.StateT $ \s ->
                          StrictST.runStateT ma s `interleave` StrictST.runStateT mb s

      (SetT ma) >>- f = SetT $ StrictST.StateT $ \s ->
                  StrictST.runStateT ma s >>- \(a,s') ->   StrictST.runStateT ( unsetT . f  $ a) s'

      ifte (SetT t) th (SetT el) = SetT $ StrictST.StateT $ \s -> ifte (StrictST.runStateT t s)
                                                  (\(a,s') -> StrictST.runStateT (unsetT . th $ a) s')
                                                  (StrictST.runStateT el s)

      once (SetT ma) = SetT $ StrictST.StateT $ \s -> once (StrictST.runStateT ma s)



-- fair choices
logicSum :: MonadLogic m => [m a] -> m a
logicSum [] = mzero
logicSum (ma : as) = ma `interleave` logicSum as

getNeighbors :: Position -> (Map.Map Position Label) -> GridM [Position]
getNeighbors pos@(Position x y ) grid =
    do
      --- should we check that Pos isn't visited yet?
      possiblePositions <- flip filterA offsets   (\ coord ->
                  do b <- isMember coord ;
                     if b then return  False -- we dont want visited neighbors
                        else return $ Map.member coord grid
                      )
      addMember pos -- add the current Label to visited set
      return possiblePositions --
  where
    offsets :: [Position]
    offsets = [(Position x (y + 1)),(Position (x + 1) y),(Position (x- 1) y), Position x (y - 1)]

extendPath :: Graph -> Position -> GridM [Position]
extendPath graph pos = do
  push pos
  if (Map.lookup pos graph) == (Just End) then
    getStack
  else do
    neighbors <- getNeighbors pos graph
    logicSum $ flip fmap neighbors $ (\neighbor -> extendPath graph neighbor)

constructPath :: (Map.Map Position Label) -> Maybe [Position]
constructPath graph = runMonads $ do
  (once . logicSum . Prelude.map return)
   (Prelude.filter (\(_, v) -> v == Start) $ Map.toList graph)
    >>= (\(startPos, _) -> do
      push startPos
      neighbors <- getNeighbors startPos graph
      logicSum $ flip fmap neighbors $ (\neighbor -> extendPath graph neighbor)
   )

runMonads :: forall a. (SetT Position (LogicT (State [Position]))) a -> Maybe a
runMonads (SetT ms) = listToMaybe $ fst $ runIdentity $ flip runStateT ([] :: [Position]) $
                                ((observeAllT $ fmap fst $ flip runStateT (Set.empty :: Set Position) ms) :: State ([Position]) [a])

main :: IO ()
main = do
         print $ constructPath board
