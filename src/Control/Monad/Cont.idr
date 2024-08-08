||| API based on
||| https://hackage.haskell.org/package/mtl-2.3.1/docs/Control-Monad-Cont.html.
module Control.Monad.Cont

import Control.Monad.Identity

public export
interface Monad m => MonadCont m where
  callCC : ((a -> m b) -> m a) -> m a

public export
record ContT (r : k) (m : k -> Type) a where
  constructor MkContT
  runContT : (a -> m r) -> m r

export
Functor (ContT r m) where
  map f fa = MkContT $ \k => runContT fa (k . f)

export
mapContT : {0 r : k} -> (m r -> m r) -> ContT r m a -> ContT r m a
mapContT f m = MkContT (f . runContT m)

export
Applicative (ContT r m) where
  pure a = MkContT (\f => f a)

  f <*> fa = MkContT $ \k => runContT f $ \f' => runContT fa $ \fa' => k (f' fa')

export
Monad (ContT r m) where
  fa >>= f = MkContT $ \k => runContT fa $ \fa' => runContT (f fa') k

export
MonadCont (ContT r m) where
  callCC f = MkContT $ \k => runContT (f (\x => MkContT (\_ => k x))) k

public export
Cont : Type -> Type -> Type
Cont r = ContT r Identity

export
runCont : Cont r a -> (a -> r) -> r
runCont m k = runIdentity $ runContT m (pure . k)
