module Syntax.Raw.MetaSubstitution where

open import Data.Sum
open import Data.Empty
open import Function
open import Utils
open import Syntax.Raw.Term
open import Syntax.Raw.Substitution
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Syntax.Raw.Context

_⟨_↦_⟩ : Term → ℕ → Term → Term
Free x ⟨ n ↦ a ⟩ with x ≟ n
Free x ⟨ n ↦ a ⟩ | yes p = a
Free x ⟨ n ↦ a ⟩ | no ¬p = Free x
Bound x ⟨ n ↦ a ⟩ = Bound x
Lam t ⟨ n ↦ a ⟩ = Lam (t ⟨ n ↦ a ⟩)
(t · s) ⟨ n ↦ a ⟩ = t ⟨ n ↦ a ⟩ · s ⟨ n ↦ a ⟩
Zero ⟨ n ↦ a ⟩ = Zero
Succ t ⟨ n ↦ a ⟩ = Succ (t ⟨ n ↦ a ⟩)
Rec z s t ⟨ n ↦ a ⟩ = 
  Rec (z ⟨ n ↦ a ⟩) (s ⟨ n ↦ a ⟩) (t ⟨ n ↦ a ⟩)

sngl-msub : ∀ {s} n → Free n ⟨ n ↦ s ⟩ ≡ s
sngl-msub n with n ≟ n
sngl-msub n | yes p = refl
sngl-msub n | no ¬p = ⊥-elim (¬p refl)

null-lsub : ∀{n t s} → Szₗ n t → t ⟨ n ↦ s ⟩ ≡ t
null-lsub (tmlFree {n} {x} p) with x ≟ suc n
null-lsub (tmlFree {n} {x} p) | yes p₁ rewrite p₁ =
  ⊥-elim (absurde _ _ p (≤refl _))
null-lsub (tmlFree {n} {x} p) | no ¬p = refl
null-lsub tmlVar = refl
null-lsub (tmlLam tm) = cong Lam (null-lsub tm)
null-lsub (tmlApp tm tm₁) = cong₂ _·_ (null-lsub tm) (null-lsub tm₁)
null-lsub tmlZero = refl
null-lsub (tmlSucc tm) = cong Succ (null-lsub tm)
null-lsub (tmlRec tm tm₁ tm₂) =
  cong₃ Rec (null-lsub tm) (null-lsub tm₁) (null-lsub tm₂)
