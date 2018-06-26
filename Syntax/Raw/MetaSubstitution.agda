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

--------------------------------------------------------------------------------
-- Meta-substitution

-- data MetaSubst : Set where
--   ⟨⟩  : MetaSubst
--   _,_ : MetaSubst → Term → MetaSubst

-- msLen : MetaSubst → ℕ
-- msLen ⟨⟩ = 0
-- msLen (σ , x) = suc (msLen σ)

-- msub-var : ℕ → MetaSubst → Term
-- msub-var x ⟨⟩ = Free x
-- msub-var x (σ , t) with x ≟ msLen σ
-- msub-var x (σ , t) | yes p = t
-- msub-var x (σ , t) | no ¬p = msub-var x σ

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

-- msub : Term → MetaSubst → Term
-- msub (Free x) σ = msub-var x σ
-- msub (Bound x) σ = Bound x
-- msub (Lam t) σ = Lam (msub t σ)
-- msub (t · s) σ = msub t σ · msub s σ
-- msub Zero σ = Zero
-- msub (Succ t) σ = Succ (msub t σ)
-- msub (Rec z s t) σ = Rec (msub z σ) (msub s σ) (msub t σ)

-- [_↦_] : ℕ → Term → MetaSubst
-- [ zero ↦ s ] = ⟨⟩ , s
-- [ suc n ↦ s ] = [ n ↦ Free n ] , s

-- [↦]len : ∀{s} n → suc n ≡ msLen [ n ↦ s ]
-- [↦]len zero = refl
-- [↦]len (suc n) = cong suc ([↦]len n)

sngl-msub : ∀ {s} n → Free n ⟨ n ↦ s ⟩ ≡ s
sngl-msub n with n ≟ n
sngl-msub n | yes p = refl
sngl-msub n | no ¬p = ⊥-elim (¬p refl)

-- sngl-msub zero = refl
-- sngl-msub (suc n) with suc n ≟ msLen [ n ↦ Free n ]
-- sngl-msub (suc n) | yes p = refl
-- sngl-msub (suc n) | no ¬p = ⊥-elim (¬p ([↦]len n))

-- null-sngl-msub : ∀ x n → x ≤ n → msub-var x [ n ↦ Free n ] ≡ Free x
-- null-sngl-msub .0 zero z≤n = refl
-- null-sngl-msub x (suc n) p with x ≟ msLen [ n ↦ Free n ]
-- null-sngl-msub x (suc n) p | yes q = cong Free (trans ([↦]len {Free n} n) (sym q))
-- null-sngl-msub x (suc n) p | no ¬p with ≤case p
-- null-sngl-msub x (suc n) p | no ¬p | inj₁ q = ⊥-elim (¬p (trans q ([↦]len n)))
-- null-sngl-msub x (suc n) p | no ¬p | inj₂ (s≤s q) = null-sngl-msub x n q

null-lsub : ∀{n t s} → Tmₗ n t → t ⟨ n ↦ s ⟩ ≡ t
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



-- null-msub : ∀{n t s} → Tmₗ n t → msub t [ n ↦ s ] ≡ t
-- null-msub (tmlFree {n} {x} p) = null-msub-var _ _ p
-- null-msub tmlVar = refl
-- null-msub (tmlLam tm) = cong Lam (null-msub tm)
-- null-msub (tmlApp tm tm₁) = cong₂ _·_ (null-msub tm) (null-msub tm₁)
-- null-msub tmlZero = refl
-- null-msub (tmlSucc tm) = cong Succ (null-msub tm)
-- null-msub (tmlRec tm tm₁ tm₂) =
--   cong₃ Rec (null-msub tm) (null-msub tm₁) (null-msub tm₂)

-- idmsub : (Θ : Ctxt) → MetaSubst
-- idmsub ◇ = ⟨⟩
-- idmsub (Θ # A) = idmsub Θ , Free (clen Θ)

-- idmsub-len : ∀{Θ} → msLen (idmsub Θ) ≡ clen Θ
-- idmsub-len {◇} = refl
-- idmsub-len {Θ # x} = cong suc idmsub-len

-- id-msub : ∀ {Θ} t → msub t (idmsub Θ) ≡ t
-- id-msub {◇} (Free x) = refl
-- id-msub {Θ # x₁} (Free x) with x ≟ msLen (idmsub Θ)
-- id-msub {Θ # x₁} (Free x) | yes p = cong Free (sym (trans p idmsub-len))
-- id-msub {Θ # x₁} (Free x) | no ¬p = id-msub {Θ} (Free x)
-- id-msub (Bound x) = refl
-- id-msub (Lam t) = cong Lam (id-msub t)
-- id-msub (t · t₁) = cong₂ _·_ (id-msub t) (id-msub t₁)
-- id-msub Zero = refl
-- id-msub (Succ t) = cong Succ (id-msub t)
-- id-msub (Rec t t₁ t₂) = cong₃ Rec (id-msub t) (id-msub t₁) (id-msub t₂)

-- --------------------------------------------------------------------------------
-- -- Closed meta-substitutions

-- data ClosedMS : MetaSubst → Set where
--   cmsEmpty : ClosedMS ⟨⟩
--   cmsCons  : ∀{σ t} → ClosedMS σ → Tm 0 t → ClosedMS (σ , t)

-- tm0msub : ∀ {σ} x → ClosedMS σ → Tm 0 (msub-var x σ)
-- tm0msub x cmsEmpty = tmFree
-- tm0msub x (cmsCons {σ = σ} σp t) with x ≟ msLen σ
-- tm0msub x (cmsCons σp t) | yes p = t
-- tm0msub x (cmsCons σp t) | no ¬p = tm0msub x σp

-- msub-Tm : ∀{t σ n} → ClosedMS σ → Tm n t → Tm n (msub t σ)
-- msub-Tm σ (tmFree {x = x}) = liftTm _ (tm0msub x σ)
-- msub-Tm σ (tmVar x₁) = tmVar x₁
-- msub-Tm σ (tmLam tm) = tmLam (msub-Tm σ tm)
-- msub-Tm σ (tmApp tm tm₁) = tmApp (msub-Tm σ tm) (msub-Tm σ tm₁)
-- msub-Tm σ tmZero = tmZero
-- msub-Tm σ (tmSucc tm) = tmSucc (msub-Tm σ tm)
-- msub-Tm σ (tmRec tm tm₁ tm₂) =
--   tmRec (msub-Tm σ tm) (msub-Tm σ tm₁) (msub-Tm σ tm₂)

-- cmsub-var : ∀{σ} x → ClosedMS σ → Tm 0 (msub-var x σ)
-- cmsub-var x cmsEmpty = tmFree
-- cmsub-var x (cmsCons {σ = σ} σp t) with x ≟ msLen σ
-- cmsub-var x (cmsCons σp t) | yes p = t
-- cmsub-var x (cmsCons σp t) | no ¬p = cmsub-var x σp

-- msub-wk : ∀{σ w} t → ClosedMS σ → msub (wk t w) σ ≡ wk (msub t σ) w
-- msub-wk (Free x) σ = sym (null-wk (cmsub-var x σ))
-- msub-wk (Bound x) σ = refl
-- msub-wk (Lam t₁) σ = cong Lam (msub-wk t₁ σ)
-- msub-wk (t₁ · t₂) σ = cong₂ _·_ (msub-wk t₁ σ) (msub-wk t₂ σ)
-- msub-wk Zero σ = refl
-- msub-wk (Succ t) σ = cong Succ (msub-wk t σ)
-- msub-wk (Rec t₁ t₂ t₃) σ = cong₃ Rec (msub-wk t₁ σ) (msub-wk t₂ σ) (msub-wk t₃ σ)

-- sub-var-msub : ∀{s σ} n x → ClosedMS σ
--   → msub (sub-var x (shift n (Id , s))) σ ≡ sub-var x (shift n (Id , msub s σ))
-- sub-var-msub zero zero σ = refl
-- sub-var-msub zero (suc x) σ = refl
-- sub-var-msub (suc n) zero σ = refl
-- sub-var-msub {s} {σ} (suc n) (suc x) σp =
--   trans (msub-wk {σ} {Up Id} (sub-var x (shift n (Id , s))) σp)
--         (cong (flip wk (Up Id)) (sub-var-msub n x σp))

-- sub-msub : ∀{s σ} n t
--          → ClosedMS σ
--          → msub (sub t (shift n (Id , s))) σ
--          ≡ sub (msub t σ) (shift n (Id , msub s σ))
-- sub-msub n (Free x) σ = sym (null-sub (cmsub-var x σ))
-- sub-msub n (Bound x) σ = sub-var-msub n x σ
-- sub-msub n (Lam t) σ = cong Lam (sub-msub (suc n) t σ)
-- sub-msub n (t₁ · t₂) σ =
--   cong₂ _·_ (sub-msub n t₁ σ) (sub-msub n t₂ σ)
-- sub-msub n Zero σ = refl
-- sub-msub n (Succ t) σ = cong Succ (sub-msub n t σ)
-- sub-msub n (Rec t₁ t₂ t₃) σ =
--   cong₃ Rec (sub-msub n t₁ σ)
--             (sub-msub n t₂ σ) (sub-msub n t₃ σ)


-- -- null-msub-var : ∀{n x s m} → x ≤ n
-- --               → msub-var x (msCons (Free m) ([ n ↦ s ]⟨ suc m ⟩)) ≡ Free (x + m)
-- -- null-msub-var z≤n = refl
-- -- null-msub-var {suc n} {suc x} {s} {m} (s≤s p) =
-- --   trans (null-msub-var {n} {x} {s} {suc m} p) (cong Free (plus-succ x m))


-- --------------------------------------------------------------------------------

-- -- [_↦_]⟨_⟩ : ℕ → Term → ℕ → MetaSubst
-- -- [ zero ↦ s ]⟨ acc ⟩ = msCons s msEmpty
-- -- [ suc n ↦ s ]⟨ acc ⟩ = msCons (Free acc) [ n ↦ s ]⟨ suc acc ⟩

-- -- [_↦_] : ℕ → Term → MetaSubst
-- -- [ n ↦ s ] = [ n ↦ s ]⟨ 0 ⟩

-- -- corr : ∀ {s acc} n → msub (Free n) ([ n ↦ s ]⟨ acc ⟩) ≡ s
-- -- corr zero = refl
-- -- corr (suc n) = corr n

-- -- null-msub-var : ∀{n x s m} → x ≤ n
-- --               → msub-var x (msCons (Free m) ([ n ↦ s ]⟨ suc m ⟩)) ≡ Free (x + m)
-- -- null-msub-var z≤n = refl
-- -- null-msub-var {suc n} {suc x} {s} {m} (s≤s p) =
-- --   trans (null-msub-var {n} {x} {s} {suc m} p) (cong Free (plus-succ x m))

-- -- null-msub : ∀{n t s} → Tmₗ n t → msub t [ n ↦ s ] ≡ t
-- -- null-msub (tmlFree {n} {x} p) =
-- --   trans (null-msub-var {n} {x} {_} {0} p) (cong Free (plus-0 x))
-- -- null-msub tmlVar = refl
-- -- null-msub (tmlLam tm) = cong Lam (null-msub tm)
-- -- null-msub (tmlApp tm tm₁) = cong₂ _·_ (null-msub tm) (null-msub tm₁)
-- -- null-msub tmlZero = refl
-- -- null-msub (tmlSucc tm) = cong Succ (null-msub tm)
-- -- null-msub (tmlRec tm tm₁ tm₂) =
-- --   cong₃ Rec (null-msub tm) (null-msub tm₁) (null-msub tm₂)
