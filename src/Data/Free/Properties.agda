module Data.Free.Properties where

open import Data.Free
open import Haskell.Prelude hiding (pure)
open import Equational

instance
    iFunctor_toFunctor : {F : PosFunctor} → Functor (toFunctor F)
    iFunctor_toFunctor {F = F} = iFunctorPosFunctor F

monad-left-id : {F : PosFunctor} → {A B : Set} 
              → (a : A) → (f : A → Free F B) → (pure a >>= f) ≡ f a
monad-left-id a f = refl


monad-right-id : {F : PosFunctor} → {A : Set} → (m : Free F A) → m >>= return ≡ m
fmap-bind-into-return-is-id : {F : PosFunctor} → {A : Set} 
                            → (fa : (toFunctor F) (Free F A)) → fmap (_>>= return) fa ≡ fa

fmap-bind-into-return-is-id {F = pList} [] = refl
fmap-bind-into-return-is-id {F = pList} (x ∷ ffa) = 
    begin
        (x >>= return) ∷ fmap (_>>= return) ffa
    =⟨ cong (_∷ fmap (_>>= return) ffa) (monad-right-id x) ⟩
        x ∷ fmap (_>>= return) ffa
    =⟨ cong (x ∷_) (fmap-bind-into-return-is-id ffa) ⟩
        x ∷ ffa
    end

fmap-bind-into-return-is-id {F = pMaybe} Nothing = refl
fmap-bind-into-return-is-id {F = pMaybe} (Just x) = 
    begin
        fmap (_>>= return) (Just x)
    =⟨⟩
        Just (x >>= pure)
    =⟨ cong (λ a → Just a) (monad-right-id x) ⟩
        (Just x)
    end

monad-right-id (pure x)  = refl
monad-right-id (free fa) =
    begin
        free (fmap (_>>= pure) fa)
    =⟨ cong free $ fmap-bind-into-return-is-id fa ⟩
        free fa
    end


