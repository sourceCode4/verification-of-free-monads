module Data.Free where

open import Level
open import Haskell.Prelude hiding (pure)
import Haskell.Prelude using (pure)
open import Data.Container.Core
import Haskell.Prim.Functor as Functor

data Free { s p : Level } (F : Container s p) (A : Set) : Set (s ⊔ p) where
    pure : A → Free F A
    free : ⟦ F ⟧ (Free F A) → Free F A

instance
    {-# TERMINATING #-}
    iFunctorFree : {F : Container _ _} → ⦃ Functor ⟦ F ⟧ ⦄ → Functor (Free F)
    iFunctorFree .fmap {a = A} {b = B} f = go
        where
            go : {F : Container _ _} → ⦃ Functor ⟦ F ⟧ ⦄ → Free F A → Free F B
            go (pure v)   = pure $ f v
            go (free ffa) = free (go <$> ffa)

    {-# TERMINATING #-}
    iApplicativeFree : {F : Container _ _} → ⦃ Functor ⟦ F ⟧ ⦄ → Applicative (Free F)
    iApplicativeFree .Applicative.pure  = pure
    iApplicativeFree ._<*>_ (pure f) (pure b)   = pure (f b)
    iApplicativeFree ._<*>_ (pure f) (free ffb) = free $ fmap f <$> ffb
    iApplicativeFree ._<*>_ (free ffa) mb       = free $ (_<*> mb) <$> ffa

    {-# TERMINATING #-}
    iMonadFree : {F : Container _ _} → ⦃ Functor ⟦ F ⟧ ⦄ → Monad (Free F)
    iMonadFree ._>>=_ (pure a)  f = f a
    iMonadFree ._>>=_ (free fa) f = free (fmap (_>>= f) fa)