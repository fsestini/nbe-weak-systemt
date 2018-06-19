module Semantics.Soundness.SubLogicalRelation where

open import Data.Maybe
open import Syntax
open import Semantics.Domain.Domain
open import Data.Product renaming (_,_ to _,,_)
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Semantics.Soundness.LogicalRelation

infix 4 _∷_⊢ₛ_®_∶_
data _∷_⊢ₛ_®_∶_ (Θ : Ctxtₗ) : Ctxt → Subst → Subst → Ctxt → Set where
  ◇® : ∀{Γ σ ρ} → Θ ∷ Γ ⊢ₛ σ ∶ ◇ → Θ ∷ Γ ⊢ₛ σ ® ρ ∶ ◇
  #® : ∀{Γ Δ A σ ρ t} {a : D}
     → Θ ∷ Γ ⊢ₛ σ ® ρ ∶ Δ
     → Θ ∷ Γ ⊢ t ® a ∶ A
     → Θ ∷ Γ ⊢ₛ σ , t ® ρ , a ∶ Δ # A
  ·® : ∀{Γ ∇ Δ σ ρ w}
     → Θ ∷ Γ ⊢ₛ σ ® ρ ∶ Δ → ∇ ⊢ᵣ w ∶ Γ → Θ ∷ ∇ ⊢ₛ σ · w ® ρ · w ∶ Δ

derₛ : ∀{Θ Γ Δ σ ρ} → Θ ∷ Γ ⊢ₛ σ ® ρ ∶ Δ → Θ ∷ Γ ⊢ₛ σ ∶ Δ
derₛ (◇® x) = x
derₛ (#® rel x) = ⊢Cons (derₛ rel) (der x)
derₛ (·® rel x) = ⊢Wk x (derₛ rel)
