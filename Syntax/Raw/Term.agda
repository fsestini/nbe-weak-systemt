module Syntax.Raw.Term where

open import Data.Product
open import Data.Nat
open import Data.Empty
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Utils

cong₃ : {A B C D : Set} {x x' : A} {y y' : B} {z z' : C}
      → (f : A → B → C → D)
      → x ≡ x' → y ≡ y' → z ≡ z'
      → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

data Term : Set where
  Free : ℕ → Term     -- De Bruijn levels
  Bound : ℕ → Term    -- De Bruijn indices
  Lam : Term → Term
  _·_ : Term → Term → Term
  Zero : Term
  Succ : Term → Term
  Rec  : Term → Term → Term → Term
infixl 7 _·_

Succ-inj : ∀{t s} → Succ t ≡ Succ s → t ≡ s
Succ-inj refl = refl

data Sz : ℕ → Term → Set where
  tmFree : ∀{n x} → Sz n (Free x)
  tmVar  : ∀{n x} → x ≤ n → Sz (suc n) (Bound x)
  tmLam  : ∀{t n} → Sz (suc n) t → Sz n (Lam t)
  tmApp  : ∀{t s n} → Sz n t → Sz n s → Sz n (t · s)
  tmZero : ∀{n} → Sz n Zero
  tmSucc : ∀{n t} → Sz n t → Sz n (Succ t)
  tmRec  : ∀{n z s t} → Sz n z → Sz n s → Sz n t → Sz n (Rec z s t)

data Szₗ : ℕ → Term → Set where
  tmlFree : ∀{n x} → x ≤ n → Szₗ (suc n) (Free x)
  tmlVar  : ∀{n x} → Szₗ n (Bound x)
  tmlLam  : ∀{t n} → Szₗ n t → Szₗ n (Lam t)
  tmlApp  : ∀{t s n} → Szₗ n t → Szₗ n s → Szₗ n (t · s)
  tmlZero : ∀{n} → Szₗ n Zero
  tmlSucc : ∀{n t} → Szₗ n t → Szₗ n (Succ t)
  tmlRec  : ∀{n z s t} → Szₗ n z → Szₗ n s → Szₗ n t → Szₗ n (Rec z s t)

data ¬Sz : ℕ → Term → Set where
  ¬tmVar : ∀{n x} → x ≥ n → ¬Sz n (Bound x)
  ¬tmLam : ∀{t n} → ¬Sz (suc n) t → ¬Sz n (Lam t)
  ¬tmApp₁ : ∀{t s n} → ¬Sz n t → ¬Sz n (t · s)
  ¬tmApp₂ : ∀{t s n} → Sz n t → ¬Sz n s → ¬Sz n (t · s)
  ¬tmSucc : ∀{t n} → ¬Sz n t → ¬Sz n (Succ t)
  ¬tmRec₁ : ∀{z s t n} → ¬Sz n z → ¬Sz n (Rec z s t)
  ¬tmRec₂ : ∀{z s t n} → Sz n z → ¬Sz n s → ¬Sz n (Rec z s t)
  ¬tmRec₃ : ∀{z s t n} → Sz n z → Sz n s → ¬Sz n t → ¬Sz n (Rec z s t)

Sz≡ : ∀{t s n m} → t ≡ s → n ≡ m → Sz n t → Sz m s
Sz≡ refl refl tm = tm

¬Sz≡ : ∀{t s n m} → t ≡ s → n ≡ m → ¬Sz n t → ¬Sz m s
¬Sz≡ refl refl tm = tm

tmSuccLemma : ∀{t n} → Sz n (Succ t) → Sz n t
tmSuccLemma (tmSucc tm) = tm

liftSz : ∀{t n} m → Sz n t → Sz (n + m) t
liftSz m tmFree = tmFree
liftSz m (tmVar x) = tmVar (≤+ _ x)
liftSz m (tmLam {n = n} tm) rewrite sym (plus-succ n m) = tmLam (liftSz m tm)
liftSz m (tmApp tm tm') = tmApp (liftSz m tm) (liftSz m tm')
liftSz m tmZero = tmZero
liftSz m (tmSucc tm) = tmSucc (liftSz m tm)
liftSz m (tmRec tm tm₁ tm₂) = tmRec (liftSz m tm) (liftSz m tm₁) (liftSz m tm₂)

¬Sz-lemma : ∀{n t} → ¬Sz n t → Sz n t → ⊥
¬Sz-lemma (¬tmVar p) (tmVar q) = absurde _ _ p q
¬Sz-lemma (¬tmLam ¬tm) (tmLam tm) = ¬Sz-lemma ¬tm tm
¬Sz-lemma (¬tmApp₁ ¬tm) (tmApp tm _) = ¬Sz-lemma ¬tm tm
¬Sz-lemma (¬tmApp₂ x ¬tm) (tmApp _ tm) = ¬Sz-lemma ¬tm tm
¬Sz-lemma (¬tmSucc tm) (tmSucc tm') = ¬Sz-lemma tm tm'
¬Sz-lemma (¬tmRec₁ tm) (tmRec tm' tm'' tm''') = ¬Sz-lemma tm tm'
¬Sz-lemma (¬tmRec₂ x tm) (tmRec tm' tm'' tm''') = ¬Sz-lemma tm tm''
¬Sz-lemma (¬tmRec₃ x x₁ tm) (tmRec tm' tm'' tm''') = ¬Sz-lemma tm tm'''

decSz : ∀ n → (t : Term) → Sz n t ⊎ ¬Sz n t
decSz n (Free x) = inj₁ tmFree
decSz n (Bound x) with suc x ≤? n
decSz .(suc _) (Bound x) | yes (s≤s p) = inj₁ (tmVar p)
decSz n (Bound x) | no ¬p with qwerty _ _ ¬p
decSz n (Bound x) | no ¬p | s≤s w = inj₂ (¬tmVar w)
decSz n (Lam t) with decSz (suc n) t
decSz n (Lam t) | inj₁ x = inj₁ (tmLam x)
decSz n (Lam t) | inj₂ y = inj₂ (¬tmLam y)
decSz n (t · s) with decSz n t | decSz n s
decSz n (t · s) | inj₁ x | inj₁ x₁ = inj₁ (tmApp x x₁)
decSz n (t · s) | inj₁ x | inj₂ y = inj₂ (¬tmApp₂ x y)
decSz n (t · s) | inj₂ y | _ = inj₂ (¬tmApp₁ y)
decSz n Zero = inj₁ tmZero
decSz n (Succ t) with decSz n t
decSz n (Succ t) | inj₁ x = inj₁ (tmSucc x)
decSz n (Succ t) | inj₂ y = inj₂ (¬tmSucc y)
decSz n (Rec z s t) with decSz n z | decSz n s | decSz n t
decSz n (Rec z s t) | inj₁ x | inj₁ x₁ | inj₁ x₂ = inj₁ (tmRec x x₁ x₂)
decSz n (Rec z s t) | inj₁ x | inj₁ x₁ | inj₂ y = inj₂ (¬tmRec₃ x x₁ y)
decSz n (Rec z s t) | inj₁ x | inj₂ y | _ = inj₂ (¬tmRec₂ x y)
decSz n (Rec z s t) | inj₂ y | _ | _ = inj₂ (¬tmRec₁ y)

inj-tmApp₂ : ∀{t n s} → ¬Sz n s → ¬Sz n (t · s)
inj-tmApp₂ {t} {n} tm with decSz n t
inj-tmApp₂ tm | inj₁ x = ¬tmApp₂ x tm
inj-tmApp₂ tm | inj₂ y = ¬tmApp₁ y

inj-tmRec₂ : ∀{z n s t} → ¬Sz n s → ¬Sz n (Rec z s t)
inj-tmRec₂ {z} {n} tm with decSz n z
inj-tmRec₂ tm | inj₁ x = ¬tmRec₂ x tm
inj-tmRec₂ tm | inj₂ y = ¬tmRec₁ y

inj-tmRec₃ : ∀{z s n t} → ¬Sz n t → ¬Sz n (Rec z s t)
inj-tmRec₃ {z} {s} {n} tm with decSz n z | decSz n s
inj-tmRec₃ tm | inj₁ x | inj₁ x₁ = ¬tmRec₃ x x₁ tm
inj-tmRec₃ tm | inj₁ x | inj₂ y = ¬tmRec₂ x y
inj-tmRec₃ tm | inj₂ y | _ = ¬tmRec₁ y

¬Sz-lemma' : ∀{n t} → (Sz n t → ⊥) → ¬Sz n t
¬Sz-lemma' {t = Free x} h = ⊥-elim (h tmFree)
¬Sz-lemma' {n} {Bound x} h with n ≤? x
¬Sz-lemma' {n} {Bound x} h | yes p = ¬tmVar p
¬Sz-lemma' {zero} {Bound x} h | no ¬p = ⊥-elim (¬p z≤n)
¬Sz-lemma' {suc n} {Bound x} h | no ¬p with qwerty _ _ ¬p
¬Sz-lemma' {suc n} {Bound x} h | no ¬p | s≤s w = ⊥-elim (h (tmVar w))
¬Sz-lemma' {t = Zero} h = ⊥-elim (h tmZero)
¬Sz-lemma' {n} {Succ t} h with decSz n t
¬Sz-lemma' h | inj₁ x = ⊥-elim (h (tmSucc x))
¬Sz-lemma' h | inj₂ y = ¬tmSucc y
¬Sz-lemma' {n} {Lam t} h with decSz (suc n) t
¬Sz-lemma' h | inj₁ x = ⊥-elim (h (tmLam x))
¬Sz-lemma' h | inj₂ y = ¬tmLam y
¬Sz-lemma' {n} {t · s} h with decSz n t | decSz n s
¬Sz-lemma' h | inj₁ x | inj₁ x₁ = ⊥-elim (h (tmApp x x₁))
¬Sz-lemma' h | inj₁ x | inj₂ y = ¬tmApp₂ x y
¬Sz-lemma' h | inj₂ y | _ = ¬tmApp₁ y
¬Sz-lemma' {n} {Rec z s t} h with decSz n z | decSz n s | decSz n t
¬Sz-lemma' h | inj₁ x | inj₁ x₁ | inj₁ x₂ = ⊥-elim (h (tmRec x x₁ x₂))
¬Sz-lemma' h | inj₁ x | inj₁ x₁ | inj₂ y = ¬tmRec₃ x x₁ y
¬Sz-lemma' h | inj₁ x | inj₂ y | _ = ¬tmRec₂ x y
¬Sz-lemma' h | inj₂ y | _ | _ = ¬tmRec₁ y
