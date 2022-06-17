module Data.Free where

import Haskell.Prelude using (pure)
import Haskell.Prim.Functor as Functor
open import Agda.Builtin.Sigma using (_,_)
open import Haskell.Prelude hiding (pure; _,_)
open import Data.Container
open import Level as L

Container00 : Set₁
Container00 = Container L.zero L.zero

data Free {s p : Level} (F : Container s p) (A : Set) : Set (s ⊔ p) where
    pure : A → Free F A
    free : ⟦ F ⟧ (Free F A) → Free F A

-- definition of map for Container00 with erased implicit arguments
cmap : {@0 C : Container00} {@0 A B : Set} → (A → B) → (x : ⟦ C ⟧ A) → ⟦ C ⟧ B
cmap f (posits , vals) = (posits , f ∘ vals)

instance
    {-# TERMINATING #-}
    iFunctorFree : {@0 F : Container00} → ⦃ Functor ⟦ F ⟧ ⦄ → Functor (Free F)
    iFunctorFree .fmap {a = A} {b = B} f = go
        where
            go : {@0 F : Container00} → ⦃ Functor ⟦ F ⟧ ⦄ → Free F A → Free F B
            go (pure v)   = pure $ f v
            go (free ffa) = free (go <$> ffa)

    {-# TERMINATING #-}
    iApplicativeFree : {@0 F : Container00} → ⦃ Functor ⟦ F ⟧ ⦄ → Applicative (Free F)
    iApplicativeFree .Applicative.pure          = pure
    iApplicativeFree ._<*>_ (pure f) (pure b)   = pure (f b)
    iApplicativeFree ._<*>_ (pure f) (free ffb) = free $ fmap f <$> ffb
    iApplicativeFree ._<*>_ (free ffa) mb       = free $ (_<*> mb) <$> ffa

    {-# TERMINATING #-}
    iMonadFree : {@0 F : Container00} → ⦃ Functor ⟦ F ⟧ ⦄ → Monad (Free F)
    iMonadFree ._>>=_ (pure a)  f = f a
    iMonadFree ._>>=_ (free fa) f = free (fmap (_>>= f) fa)
    
    iFunctorContainer : {@0 C : Container00} → Functor ⟦ C ⟧
    iFunctorContainer = record { fmap = cmap }