module Syntax.Typed.Correspondence.Correspondence where

open import Syntax.Raw
open import Syntax.Typed.Equality.Equality
open import Syntax.Typed.Target
open import Syntax.Typed.Correspondence.ExplicitToImplicit
open import Syntax.Typed.Correspondence.ImplicitToExplicit

std-to-target : ∀{Θ A t s} → Θ ∷ ◇ ⊢ t ∼ s ∶ A → Θ ⊢ t ∼ s ∶ A
std-to-target eq = convert∼ eq

target-to-std : ∀{Θ A t s} → Θ ⊢ t ∼ s ∶ A → Θ ∷ ◇ ⊢ t ∼ s ∶ A
target-to-std eq = convert eq
