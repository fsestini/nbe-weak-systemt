module Syntax.Typed.Correspondence.ImplicitToExplicit where

open import Syntax.Raw
open import Syntax.Typed.Equality
open import Syntax.Typed.Target
open import Syntax.Typed.MetaSubstitution

mutual
  converts : ∀{Θ Δ σ τ} → Θ ⊢ₛ σ ∼ τ ∶ Δ → Θ ⊢ₗ σ ∼ τ ∶ Δ
  converts ∼empty = ⊢⟨⟩
  converts (∼cons s x) = ⊢Cons (convert x) (converts s)

  convert : ∀{Θ A t s} → Θ ⊢ t ∼ s ∶ A → Θ ∷ ◇ ⊢ t ∼ s ∶ A
  convert (∼refl x) = ∼refl x
  convert (∼symm eq) = ∼symm (convert eq)
  convert (∼trans eq eq₁) = ∼trans (convert eq) (convert eq₁)
  convert (∼β x x₁) = ~⟶ (⟶β x x₁)
  convert (∼recZ x x₁) = ~⟶ (⟶recZ x x₁)
  convert (∼recS x x₁ x₂) = ~⟶ (⟶recS x x₁ x₂)
  convert (∼sub td σ) = ∼msub td (converts σ)
