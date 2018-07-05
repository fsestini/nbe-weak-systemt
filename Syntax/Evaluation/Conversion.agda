module Syntax.Evaluation.Conversion where

open import Relation.Nullary
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat
open import Data.Empty
open import Syntax.Raw
open import Syntax.Evaluation.Evaluation
open import Syntax.Evaluation.SubSwap
open import Syntax.Evaluation.NormalForm
open import Relation.Binary.PropositionalEquality
open import Relation public

infix 4 _⟶ʷ_
data _⟶ʷ_ : Term → Term → Set where
  ⟶β : ∀{t s} → β-Redex (Lam t) s → Lam t · s ⟶ʷ sub t (Id , s)
  ⟶RZ : ∀{z s} → N-Redex z s Zero → Rec z s Zero ⟶ʷ z
  ⟶RS : ∀{z s t} → N-Redex z s (Succ t) → Rec z s (Succ t) ⟶ʷ s · t · Rec z s t
  ⟶s : ∀{t a b n} → a ⟶ʷ b → t ⟨ n ↦ a ⟩ ⟶ʷ t ⟨ n ↦ b ⟩

infix 4 _⟶ᶜʰ_
data _⟶ᶜʰ_ : Term → Term → Set where
  ⟶ᶜʰβ : ∀{t s} → β-Redex (Lam t) s → Lam t · s ⟶ᶜʰ sub t (Id , s)
  ⟶ᶜʰRZ : ∀{z s} → N-Redex z s Zero → Rec z s Zero ⟶ᶜʰ z
  ⟶ᶜʰRS : ∀{z s t} → N-Redex z s (Succ t) → Rec z s (Succ t) ⟶ᶜʰ s · t · Rec z s t
  ⟶ᶜʰξ : ∀{t t'} → t ⟶ᶜʰ t' → Lam t ⟶ᶜʰ Lam t'
  ⟶ᶜʰS : ∀{t t'} → t ⟶ᶜʰ t' → Succ t ⟶ᶜʰ Succ t'
  ⟶ᶜʰR₁ : ∀{z z' s t} → z ⟶ᶜʰ z' → Rec z s t ⟶ᶜʰ Rec z' s t
  ⟶ᶜʰR₂ : ∀{z s s' t} → s ⟶ᶜʰ s' → Rec z s t ⟶ᶜʰ Rec z s' t
  ⟶ᶜʰR₃ : ∀{z s t t'} → t ⟶ᶜʰ t' → Rec z s t ⟶ᶜʰ Rec z s t'
  ⟶ᶜʰ·₁ : ∀{t t' s} → t ⟶ᶜʰ t' → t · s ⟶ᶜʰ t' · s
  ⟶ᶜʰ·₂ : ∀{t s s'} → s ⟶ᶜʰ s' → t · s ⟶ᶜʰ t · s'

mutual

  ifNe : ∀{t} → Ne t → ¬ (Σ Term λ s → t ⟶ᶜʰ s)
  ifNe (neApp () _ _ _) (_ ,, ⟶ᶜʰβ _)
  ifNe (neApp ne _ _ _) (_ ,, ⟶ᶜʰ·₁ r) = ifNe ne (_ ,, r)
  ifNe (neApp ne x x₁ x₂) (_ ,, ⟶ᶜʰ·₂ r) = ifNf x (_ ,, r)
  ifNe (neApp₁ x x₁ x₂) (_ ,, ⟶ᶜʰβ (βrdx x₃ x₄)) = ¬Sz-lemma x₂ (tmLam x₃)
  ifNe (neApp₁ x x₁ x₂) (_ ,, ⟶ᶜʰ·₁ r) = ifNf x (_ ,, r)
  ifNe (neApp₁ x x₁ x₂) (_ ,, ⟶ᶜʰ·₂ r) = ifNf x₁ (_ ,, r)
  ifNe (neApp₂ x x₁ x₂ x₃) (_ ,, ⟶ᶜʰβ (βrdx x₄ x₅)) = ¬Sz-lemma x₃ x₅
  ifNe (neApp₂ x x₁ x₂ x₃) (_ ,, ⟶ᶜʰ·₁ r) = ifNf x (_ ,, r)
  ifNe (neApp₂ x x₁ x₂ x₃) (_ ,, ⟶ᶜʰ·₂ r) = ifNf x₁ (_ ,, r)
  ifNe (neRec x x₁ () x₂ x₃ x₄) (_ ,, ⟶ᶜʰRZ (NrdxZ x₅ x₆))
  ifNe (neRec x x₁ () x₂ x₃ x₄) (_ ,, ⟶ᶜʰRS (NrdxS x₅ x₆ x₇))
  ifNe (neRec x x₁ ne x₂ x₃ x₄) (_ ,, ⟶ᶜʰR₁ r) = ifNf x (_ ,, r)
  ifNe (neRec x x₁ ne x₂ x₃ x₄) (_ ,, ⟶ᶜʰR₂ r) = ifNf x₁ (_ ,, r)
  ifNe (neRec x x₁ ne x₂ x₃ x₄) (_ ,, ⟶ᶜʰR₃ r) = ifNe ne (_ ,, r)
  ifNe (neRec₁ x x₁ x₂ x₃) (_ ,, ⟶ᶜʰRZ (NrdxZ x₄ x₅)) = ¬Sz-lemma x₃ x₄
  ifNe (neRec₁ x x₁ x₂ x₃) (_ ,, ⟶ᶜʰRS (NrdxS x₄ x₅ x₆)) = ¬Sz-lemma x₃ x₄
  ifNe (neRec₁ x x₁ x₂ x₃) (_ ,, ⟶ᶜʰR₁ r) = ifNf x (_ ,, r)
  ifNe (neRec₁ x x₁ x₂ x₃) (_ ,, ⟶ᶜʰR₂ r) = ifNf x₁ (_ ,, r)
  ifNe (neRec₁ x x₁ x₂ x₃) (_ ,, ⟶ᶜʰR₃ r) = ifNf x₂ (_ ,, r)
  ifNe (neRec₂ x x₁ nfZero x₃ x₄) (_ ,, ⟶ᶜʰRZ (NrdxZ x₂ x₅)) = ¬Sz-lemma x₄ x₅
  ifNe (neRec₂ x x₁ (nfNe ()) x₃ x₄) (_ ,, ⟶ᶜʰRZ x₅)
  ifNe (neRec₂ x x₁ x₂ x₃ x₄) (_ ,, ⟶ᶜʰRS (NrdxS x₅ x₆ x₇)) = ¬Sz-lemma x₄ x₆
  ifNe (neRec₂ x x₁ x₂ x₃ x₄) (_ ,, ⟶ᶜʰR₁ r) = ifNf x (_ ,, r)
  ifNe (neRec₂ x x₁ x₂ x₃ x₄) (_ ,, ⟶ᶜʰR₂ r) = ifNf x₁ (_ ,, r)
  ifNe (neRec₂ x x₁ x₂ x₃ x₄) (_ ,, ⟶ᶜʰR₃ r) = ifNf x₂ (_ ,, r)
  ifNe (neRec₃ x x₁ x₂ x₃ x₄ ()) (_ ,, ⟶ᶜʰRZ x₆)
  ifNe (neRec₃ x x₁ x₂ x₃ x₄ (¬tmSucc x₅)) (_ ,, ⟶ᶜʰRS (NrdxS x₆ x₇ x₈)) = ¬Sz-lemma x₅ x₈
  ifNe (neRec₃ x x₁ x₂ x₃ x₄ x₅) (_ ,, ⟶ᶜʰR₁ r) = ifNf x (_ ,, r)
  ifNe (neRec₃ x x₁ x₂ x₃ x₄ x₅) (_ ,, ⟶ᶜʰR₂ r) = ifNf x₁ (_ ,, r)
  ifNe (neRec₃ x x₁ x₂ x₃ x₄ x₅) (_ ,, ⟶ᶜʰR₃ r) = ifNf x₂ (_ ,, r)
  ifNe neFree (_ ,, ())
  ifNe neBound (_ ,, ())

  ifNf : ∀{t} → Nf t → ¬ (Σ Term λ s → t ⟶ᶜʰ s)
  ifNf (nfLam nf) (_ ,, ⟶ᶜʰξ r) = ifNf nf (_ ,, r)
  ifNf nfZero (_ ,, ())
  ifNf (nfSucc nf) (_ ,, ⟶ᶜʰS r) = ifNf nf (_ ,, r)
  ifNf (nfNe x) (_ ,, r) = ifNe x (_ ,, r)

infix 4 _⟶*_
_⟶*_ = RTClo _⟶ᶜʰ_

⟶*-ξ : ∀{t t'} -> t ⟶* t' -> Lam t ⟶* Lam t'
⟶*-ξ (step* x) = step* (⟶ᶜʰξ x)
⟶*-ξ refl* = refl*
⟶*-ξ (trans* c c₁) = trans* (⟶*-ξ c) (⟶*-ξ c₁)

⟶*-App1 : ∀{t t' s} -> t ⟶* t' -> t · s ⟶* t' · s
⟶*-App1 (step* x) = step* (⟶ᶜʰ·₁ x)
⟶*-App1 refl* = refl*
⟶*-App1 (trans* x x₁) = trans* (⟶*-App1 x) (⟶*-App1 x₁)

⟶*-App2 : ∀{t s s'} -> s ⟶* s' -> t · s ⟶* t · s'
⟶*-App2 (step* x) = step* (⟶ᶜʰ·₂ x)
⟶*-App2 refl* = refl*
⟶*-App2 (trans* c c₁) = trans* (⟶*-App2 c) (⟶*-App2 c₁)

⟶*-Succ : ∀{t t'} → t ⟶* t' → Succ t ⟶* Succ t'
⟶*-Succ (step* x) = step* (⟶ᶜʰS x)
⟶*-Succ refl* = refl*
⟶*-Succ (trans* r r₁) = trans* (⟶*-Succ r) (⟶*-Succ r₁)

⟶*-Rec1 : ∀{z z' s t} → z ⟶* z' → Rec z s t ⟶* Rec z' s t
⟶*-Rec1 (step* x) = step* (⟶ᶜʰR₁ x)
⟶*-Rec1 refl* = refl*
⟶*-Rec1 (trans* r r₁) = trans* (⟶*-Rec1 r) (⟶*-Rec1 r₁)

⟶*-Rec2 : ∀{z s s' t} → s ⟶* s' → Rec z s t ⟶* Rec z s' t
⟶*-Rec2 (step* x) = step* (⟶ᶜʰR₂ x)
⟶*-Rec2 refl* = refl*
⟶*-Rec2 (trans* r r₁) = trans* (⟶*-Rec2 r) (⟶*-Rec2 r₁)

⟶*-Rec3 : ∀{z s t t'} → t ⟶* t' → Rec z s t ⟶* Rec z s t'
⟶*-Rec3 (step* x) = step* (⟶ᶜʰR₃ x)
⟶*-Rec3 refl* = refl*
⟶*-Rec3 (trans* r r₁) = trans* (⟶*-Rec3 r) (⟶*-Rec3 r₁)

msubrr : ∀{t a b} n → a ⟶* b → t ⟨ n ↦ a ⟩ ⟶* t ⟨ n ↦ b ⟩
msubrr {Free x} zero r  with x ≟ 0
msubrr {Free x} zero r | yes p = r
msubrr {Free x} zero r | no ¬p = refl*
msubrr {Free x} (suc n) r with x ≟ suc n
msubrr {Free x} (suc n) r | yes p = r
msubrr {Free x} (suc n) r | no ¬p = refl*
msubrr {Bound x} n r = refl*
msubrr {Lam t} n r = ⟶*-ξ (msubrr {t} n r)
msubrr {t · s} n r = 
  trans* (⟶*-App1 (msubrr {t} n r)) (⟶*-App2 (msubrr {s} n r))
msubrr {Zero} n r = refl*
msubrr {Succ t} n r = ⟶*-Succ (msubrr {t} n r)
msubrr {Rec z s t} n r =
  trans* (⟶*-Rec1 (msubrr {z} n r)) (trans* (⟶*-Rec2 (msubrr {s} n r))
  (⟶*-Rec3 (msubrr {t} n r)))

corr1 : ∀{t s} → t ⟶ʷ s → t ⟶* s
corr1 (⟶β x) = step* (⟶ᶜʰβ x)
corr1 (⟶RZ x) = step* (⟶ᶜʰRZ x)
corr1 (⟶RS x) = step* (⟶ᶜʰRS x)
corr1 (⟶s {t} {a} {b} {n} r) = msubrr {t} {a} {b} n (corr1 r)

one-step : ∀{t s} → ¬ (t ≡ s) → t ⟶* s → Σ Term λ r → t ⟶ᶜʰ r
one-step h (step* x) = _ ,, x
one-step h refl* = ⊥-elim (h refl)
one-step {t} h (trans* {_} {b} r r₁) with dec≡ t b
one-step {t} h (trans* {y = .t} r r₁) | yes refl = one-step h r₁
one-step h (trans* {y = y} r r₁) | no ¬p = one-step ¬p r

corr1' : ∀{t s} → t ⟶ʷ s → ¬ (t ≡ s) → Σ Term λ r → t ⟶ᶜʰ r
corr1' r p = one-step p (corr1 r)
