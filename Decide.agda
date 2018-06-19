module Decide where

open import Syntax
open import Semantics
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)

open ⟦_⟧≃⟦_⟧_∈tm_

decide∼ : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ∶ A → Θ ∷ Γ ⊢ s ∶ A → Dec (Θ ∷ Γ ⊢ t ∼ s ∶ A)
decide∼ {Θ} {Γ} {A} {t} {s} td sd = goal
  where
    td-s = soundness td ; sd-s = soundness sd
    goal : Dec (Θ ∷ Γ ⊢ t ∼ s ∶ A)
    goal with dec≡ (nf td) (nf sd)
    goal | yes p = yes (∼trans td-s (≡to∼L (sym p) (∼symm sd-s)))
    goal | no ¬p = no λ eq → ¬p (completeness eq td sd)

confl : ∀{Θ A t s w} → Θ ⊢ t ∼ s ∶ A → Θ ⊢ t ∼ w ∶ A
      → Σ Term λ q → Θ ⊢ s ∼ q ∶ A × Θ ⊢ w ∼ q ∶ A
confl eq1 eq2 = nf sd ,, std-to-target (soundness sd) ,,
                std-to-target (≡to∼R (sym compl) (soundness ws))
  where eq = target-to-std (∼trans (∼symm eq1) eq2)
        sd = proj₁ (∼lemma eq) ; ws = proj₂ (∼lemma eq)
        compl = completeness eq sd ws

decide∼' : ∀{Θ A t s} → Θ ⊢ t ∶ A → Θ ⊢ s ∶ A → Dec (Θ ⊢ t ∼ s ∶ A)
decide∼' td sd with decide∼ td sd
decide∼' td sd | yes p = yes (std-to-target p)
decide∼' td sd | no ¬p = no (λ x → ¬p (target-to-std x))
