module Syntax.Typed.MetaSubstitution where

open import Data.Empty
open import Data.Nat
open import Syntax.Raw
open import Syntax.Typed.Typed
open import Syntax.Typed.Equality.Equality
open import Syntax.Typed.Equality.Properties
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

⊢lsub : ∀{Θ Γ A B t a b}
      → Θ # A ∷ Γ ⊢ t ∶ B → Θ ∷ ◇ ⊢ a ∼ b ∶ A
      → Θ ∷ Γ ⊢ t ⟨ clen Θ ↦ a ⟩ ∼ t ⟨ clen Θ ↦ b ⟩ ∶ B
⊢lsub {Θ} (free {n = n} x) eq with n ≟ clen Θ
⊢lsub (free x) eq | yes p rewrite p | l-maps-here x = wk∼ eq
⊢lsub {Θ} (free {n = .(clen Θ)} here) eq | no ¬p = ⊥-elim (¬p refl)
⊢lsub {Θ} (free {n = n} (there x)) eq | no ¬p = ∼refl (free x)
⊢lsub (var x) eq = ∼refl (var x)
⊢lsub (lam td) eq = ∼ξ (⊢lsub td eq)
⊢lsub (td ● sd) eq = ∼compApp (⊢lsub td eq) (⊢lsub sd eq)
⊢lsub zZ eq = ∼refl zZ
⊢lsub (sS td) eq = ∼compSucc (⊢lsub td eq)
⊢lsub (rec td td₁ td₂) eq = 
  ∼compRec (⊢lsub td eq) (⊢lsub td₁ eq) (⊢lsub td₂ eq)
