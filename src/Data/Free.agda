module Data.Free where

open import Haskell.Prelude hiding (pure)
import Haskell.Prelude using (pure)
import Haskell.Prim.Functor as Functor

{- Add cases to extend for more functors -}
data PosFunctor : Set where
    pList : PosFunctor
    pMaybe : PosFunctor

toFunctor : PosFunctor → (Set → Set)
toFunctor pList = List
toFunctor pMaybe = Maybe

data Free (F : PosFunctor) (A : Set) : Set where
    pure : A → Free F A
    free : toFunctor F (Free F A) → Free F A

iFunctorPosFunctor : (F : PosFunctor) → Functor (toFunctor F)
iFunctorPosFunctor pList = iFunctorList
iFunctorPosFunctor pMaybe = iFunctorMaybe

instance
    {-# TERMINATING #-}
    iFunctorFree : {F : PosFunctor} → ⦃ Functor (toFunctor F) ⦄ → Functor (Free F)
    iFunctorFree .fmap {a = A} {b = B} f = go
        where
            go : {F : PosFunctor} → {{ Functor (toFunctor F) }} → Free F A → Free F B
            go (pure v)   = pure $ f v
            go (free ffa) = free (go <$> ffa)

    {-# TERMINATING #-}
    iApplicativeFree : {F : PosFunctor} → ⦃ Functor (toFunctor F) ⦄ → Applicative (Free F)
    iApplicativeFree .Applicative.pure  = pure
    iApplicativeFree ._<*>_ (pure f) (pure b)   = pure (f b)
    iApplicativeFree ._<*>_ (pure f) (free ffb) = free $ fmap f <$> ffb
    iApplicativeFree ._<*>_ (free ffa) mb       = free $ (_<*> mb) <$> ffa

    {-# TERMINATING #-}
    iMonadFree : {F : PosFunctor} → ⦃ Functor (toFunctor F) ⦄ → Monad (Free F)
    iMonadFree ._>>=_ (pure a)  f = f a
    iMonadFree ._>>=_ (free fa) f = free (fmap (_>>= f) fa)