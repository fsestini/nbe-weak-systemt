module Syntax.Typed.Target where

open import Syntax.Raw
open import Syntax.Typed.Typed
open import Syntax.Evaluation

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
    ∼sub   : ∀{Γ A B t a b} → Γ # A ⊢ t ∶ B → Γ ⊢ a ∼ b ∶ A
           → Γ ⊢ t ⟨ clen Γ ↦ a ⟩ ∼ t ⟨ clen Γ ↦ b ⟩ ∶ B

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
