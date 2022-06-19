module Data.Free.Properties where

open import Axiom.Extensionality.Propositional
open import Data.Free
open import Haskell.Prelude hiding (_,_; pure)
open import Agda.Builtin.Sigma using (_,_)
open import Equational
open import Data.Container.Core hiding (map)
open import Level as L

postulate extensionality : Extensionality L.zero L.zero

{- Right identity monad law proof -}

monad-left-id : {F : Container00} {A B : Set}
              → (a : A) → (f : A → Free F B) → (return a >>= f) ≡ f a 
monad-left-id a f = refl

{- Right identity monad law proof and its lemmas -}

monad-right-id : {F : Container00} {A : Set} → (m : Free F A) → m >>= return ≡ m

bind-into-pure-is-id : {F : Container00} {A : Set} 
                       ((s , vs) : ⟦ F ⟧ (Free F A)) → (_>>= return) ∘ vs ≡ vs
bind-into-pure-is-id c@(_ , vs) = 
    begin
        (λ p → vs p >>= pure)
    =⟨ extensionality (λ p → monad-right-id (vs p)) ⟩
        vs
    end

fmap-bind-into-return-is-id : {F : Container00} {A : Set} 
                              (fa : ⟦ F ⟧ (Free F A)) → fmap (_>>= return) fa ≡ fa
fmap-bind-into-return-is-id fa@(s , vs) = 
    begin
        -- since return is defined as pure I write it direcly
        fmap (_>>= pure) fa
    =⟨⟩ -- applying the definition of fmap for containers
        (s , (_>>= pure) ∘ vs)
       -- by the above lemma applied to the second position of the pair
    =⟨ cong (s ,_) (bind-into-pure-is-id fa) ⟩
        fa
    end

monad-right-id (pure x)  = refl
monad-right-id (free fa) =
    begin
        free (fmap (_>>= pure) fa)
    =⟨ cong free $ fmap-bind-into-return-is-id fa ⟩
        free fa
    end

{- Associativty monad law proof and its lemmas -}

monad-assoc : {F : Container00} {A B C : Set}
              (m : Free F A) (g : A → Free F B) (h : B → Free F C) 
            → (m >>= g) >>= h ≡ m >>= (λ x → g x >>= h)

ext-lemma : {F : Container00} {A B C : Set} 
            (g : A → Free F B) (h : B → Free F C) ((_ , vs) : ⟦ F ⟧ (Free F A)) 
          → ∀ x → (λ p → ((vs p) >>= g) >>= h) x ≡ (λ p → (vs p) >>= (λ x → (g x) >>= h)) x
ext-lemma g h fa@(_ , vs) p = 
    begin
        ((vs p) >>= g) >>= h
    =⟨ monad-assoc (vs p) g h ⟩
        (vs p) >>= (λ x → (g x) >>= h)
    end

fmap-bind-lemma : {F : Container00} {A B C : Set}
                  (fa : ⟦ F ⟧ (Free F A)) (g : A → Free F B) (h : B → Free F C)
                → fmap (_>>= h) (fmap (_>>= g) fa) ≡ fmap (_>>= (λ x → (g x) >>= h)) fa
fmap-bind-lemma fa@(s , vs) g h =
    begin
{-
        fmap (_>>= h) (fmap (_>>= g) fa)
    =⟨⟩
-}
        (s , λ p → (vs p >>= g) >>= h)
    =⟨ cong (s ,_) (extensionality (ext-lemma g h fa)) ⟩
        (s , λ p → (vs p) >>= (λ x → g x >>= h))
    =⟨⟩
        fmap (_>>= (λ x → g x >>= h)) fa
    end

monad-assoc (pure x) g h = refl
monad-assoc m@(free fa) g h =
    begin
        (free (fmap (_>>= g) fa)) >>= h
    =⟨⟩
        free (fmap (_>>= h) (fmap (_>>= g) fa))
    =⟨ cong free (fmap-bind-lemma fa g h) ⟩
        free (fmap (_>>= (λ x → g x >>= h)) fa)
    =⟨⟩
        (free fa) >>= (λ x → g x >>= h)
    end