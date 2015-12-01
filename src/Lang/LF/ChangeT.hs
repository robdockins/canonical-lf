module Lang.LF.ChangeT where

import Control.Monad

data ChangeT m a
  = Unchanged a
  | Changed (m a)

instance Functor m => Functor (ChangeT m) where
  fmap f (Unchanged a) = Unchanged (f a)
  fmap f (Changed x) = Changed (fmap f x)

instance Applicative m => Applicative (ChangeT m) where
  pure = Unchanged
  (Unchanged f) <*> (Unchanged x) = Unchanged (f x)
  (Unchanged f) <*> (Changed x)   = Changed (pure f <*> x)
  (Changed f)   <*> (Unchanged x) = Changed (f <*> pure x)
  (Changed f)   <*> (Changed x)   = Changed (f <*> x)

instance Monad m => Monad (ChangeT m) where
  return = Unchanged
  Unchanged x >>= f = f x
  Changed x  >>= f  = Changed (join (fmap (g . f) x))
    where g (Unchanged q) = return q
          g (Changed q) = q

runChangeT :: Monad m => ChangeT m a -> m a
runChangeT (Unchanged x) = return x
runChangeT (Changed x)   = x

mapChange :: Monad m => (a -> b) -> (a -> m b) -> ChangeT m a -> ChangeT m b
mapChange f _ (Unchanged x) = Unchanged (f x)
mapChange _ g (Changed y)   = Changed (g =<< y)

onChange :: Monad m => b -> (a -> m b) -> ChangeT m a -> ChangeT m b
onChange x = mapChange (const x)
