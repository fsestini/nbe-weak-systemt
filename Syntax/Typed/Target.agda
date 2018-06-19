module Syntax.Typed.Target where

open import Syntax.Raw
open import Syntax.Typed.Typed

infix 4 _⊢_∶_
_⊢_∶_ : Ctxtₗ → Term → Ty → Set
Θ ⊢ t ∶ A = Θ ∷ ◇ ⊢ t ∶ A

mutual

  infix 4 _⊢_∼_∶_
  data _⊢_∼_∶_ : Ctxtₗ → Term → Term → Ty → Set where

    -- Equivalence rules
    ∼refl  : ∀{Γ t A} → Γ ⊢ t ∶ A → Γ ⊢ t ∼ t ∶ A
    ∼symm  : ∀{Γ t s A} → Γ ⊢ t ∼ s ∶ A → Γ ⊢ s ∼ t ∶ A
    ∼trans : ∀{Γ t s w A} → Γ ⊢ t ∼ s ∶ A → Γ ⊢ s ∼ w ∶ A → Γ ⊢ t ∼ w ∶ A

    -- Substitution
    ∼sub   : ∀{Θ Δ A t σ τ} → Δ ∷ ◇ ⊢ t ∶ A → Θ ⊢ₛ σ ∼ τ ∶ Δ
           → Θ ⊢ msub t σ ∼ msub t τ ∶ A

    -- Computation rules
    ∼β : ∀{Γ A B t s}
       → Γ ∷ ◇ # A ⊢ t ∶ B → Γ ⊢ s ∶ A
       → Γ ⊢ Lam t · s ∼ t [ s ] ∶ B
    ∼recZ : ∀{Γ A z s}
          → Γ ⊢ z ∶ A → Γ ⊢ s ∶ N => A => A
          → Γ ⊢ Rec z s Zero ∼ z ∶ A
    ∼recS : ∀{Γ A z s n}
          → Γ ⊢ z ∶ A → Γ ⊢ s ∶ N => A => A → Γ ⊢ n ∶ N
          → Γ ⊢ Rec z s (Succ n) ∼ s · n · Rec z s n ∶ A

  infix 4 _⊢ₛ_∼_∶_
  data _⊢ₛ_∼_∶_ : Ctxtₗ → MetaSubst → MetaSubst → Ctxtₗ → Set where

    ∼empty : ∀{Θ} → Θ ⊢ₛ ⟨⟩ ∼ ⟨⟩ ∶ ◇
    ∼cons  : ∀{Θ Δ A t s σ τ} → Θ ⊢ₛ σ ∼ τ ∶ Δ → Θ ⊢ t ∼ s ∶ A
           → Θ ⊢ₛ σ , t ∼ τ , s ∶ Δ # A
