module Syntax.Typed.Equality.Equality where

open import Syntax.Raw
open import Syntax.Typed.Typed
open import Relation.Binary.PropositionalEquality hiding ([_])

infix 4 _∷_⊢_⟶_∶_
data _∷_⊢_⟶_∶_ : Ctxtₗ → Ctxt → Term → Term → Ty → Set where

  -- Computation rules
  ⟶β : ∀{Θ Γ A B t s}
     → Θ ∷ ◇ # A ⊢ t ∶ B → Θ ∷ ◇ ⊢ s ∶ A
     → Θ ∷ Γ ⊢ Lam t · s ⟶ t [ s ] ∶ B
  ⟶recZ : ∀{Θ Γ A z s}
        → Θ ∷ ◇ ⊢ z ∶ A → Θ ∷ ◇ ⊢ s ∶ N => A => A
        → Θ ∷ Γ ⊢ Rec z s Zero ⟶ z ∶ A
  ⟶recS : ∀{Θ Γ A z s n}
        → Θ ∷ ◇ ⊢ z ∶ A → Θ ∷ ◇ ⊢ s ∶ N => A => A → Θ ∷ ◇ ⊢ n ∶ N
        → Θ ∷ Γ ⊢ Rec z s (Succ n) ⟶ s · n · Rec z s n ∶ A

  -- Compatibility rules
  ⟶ξ : ∀{Θ Γ A B t t'}
       → Θ ∷ Γ # A ⊢ t ⟶ t' ∶ B
       → Θ ∷ Γ ⊢ Lam t ⟶ Lam t' ∶ A => B
  ⟶compSucc : ∀{Θ Γ t t'}
              → Θ ∷ Γ ⊢ t ⟶ t' ∶ N
              → Θ ∷ Γ ⊢ Succ t ⟶ Succ t' ∶ N

  ⟶compApp₁  : ∀{Γ Γ' r r' s A B}
               → Γ ∷ Γ' ⊢ r ⟶ r' ∶ A => B → Γ ∷ Γ' ⊢ s ∶ A
               → Γ ∷ Γ' ⊢ r · s ⟶ r' · s ∶ B
  ⟶compApp₂  : ∀{Γ Γ' r s s' A B}
               → Γ ∷ Γ' ⊢ r ∶ A => B → Γ ∷ Γ' ⊢ s ⟶ s' ∶ A
               → Γ ∷ Γ' ⊢ r · s ⟶ r · s' ∶ B

  ⟶compRec₁  : ∀{Θ Γ A z s n z'}
               → Θ ∷ Γ ⊢ z ⟶ z' ∶ A
               → Θ ∷ Γ ⊢ s ∶ N => A => A
               → Θ ∷ Γ ⊢ n ∶ N
               → Θ ∷ Γ ⊢ Rec z s n ⟶ Rec z' s n ∶ A
  ⟶compRec₂  : ∀{Θ Γ A z s n s'}
               → Θ ∷ Γ ⊢ z ∶ A
               → Θ ∷ Γ ⊢ s ⟶ s' ∶ N => A => A
               → Θ ∷ Γ ⊢ n ∶ N
               → Θ ∷ Γ ⊢ Rec z s n ⟶ Rec z s' n ∶ A
  ⟶compRec₃  : ∀{Θ Γ A z s n n'}
               → Θ ∷ Γ ⊢ z ∶ A
               → Θ ∷ Γ ⊢ s ∶ N => A => A
               → Θ ∷ Γ ⊢ n ⟶ n' ∶ N
               → Θ ∷ Γ ⊢ Rec z s n ⟶ Rec z s n' ∶ A

infix 4 _∷_⊢_∼_∶_
data _∷_⊢_∼_∶_ : Ctxtₗ → Ctxt → Term → Term → Ty → Set where

  ~⟶ : ∀{Γ Γ' t s A} -> Γ ∷ Γ' ⊢ t ⟶ s ∶ A → Γ ∷ Γ' ⊢ t ∼ s ∶ A

  -- Equivalence rules
  ∼refl  : ∀{Γ Γ' t A} → Γ ∷ Γ' ⊢ t ∶ A → Γ ∷ Γ' ⊢ t ∼ t ∶ A
  ∼symm  : ∀{Γ Γ' t s A} → Γ ∷ Γ' ⊢ t ∼ s ∶ A → Γ ∷ Γ' ⊢ s ∼ t ∶ A
  ∼trans : ∀{Γ Γ' t s w A} → Γ ∷ Γ' ⊢ t ∼ s ∶ A → Γ ∷ Γ' ⊢ s ∼ w ∶ A
         → Γ ∷ Γ' ⊢ t ∼ w ∶ A
