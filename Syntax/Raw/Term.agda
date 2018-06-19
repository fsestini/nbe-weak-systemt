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

data Tm : ℕ → Term → Set where
  tmFree : ∀{n x} → Tm n (Free x)
  tmVar  : ∀{n x} → x ≤ n → Tm (suc n) (Bound x)
  tmLam  : ∀{t n} → Tm (suc n) t → Tm n (Lam t)
  tmApp  : ∀{t s n} → Tm n t → Tm n s → Tm n (t · s)
  tmZero : ∀{n} → Tm n Zero
  tmSucc : ∀{n t} → Tm n t → Tm n (Succ t)
  tmRec  : ∀{n z s t} → Tm n z → Tm n s → Tm n t → Tm n (Rec z s t)

data Tmₗ : ℕ → Term → Set where
  tmlFree : ∀{n x} → x ≤ n → Tmₗ (suc n) (Free x)
  tmlVar  : ∀{n x} → Tmₗ n (Bound x)
  tmlLam  : ∀{t n} → Tmₗ n t → Tmₗ n (Lam t)
  tmlApp  : ∀{t s n} → Tmₗ n t → Tmₗ n s → Tmₗ n (t · s)
  tmlZero : ∀{n} → Tmₗ n Zero
  tmlSucc : ∀{n t} → Tmₗ n t → Tmₗ n (Succ t)
  tmlRec  : ∀{n z s t} → Tmₗ n z → Tmₗ n s → Tmₗ n t → Tmₗ n (Rec z s t)

data ¬Tm : ℕ → Term → Set where
  ¬tmVar : ∀{n x} → x ≥ n → ¬Tm n (Bound x)
  ¬tmLam : ∀{t n} → ¬Tm (suc n) t → ¬Tm n (Lam t)
  ¬tmApp₁ : ∀{t s n} → ¬Tm n t → ¬Tm n (t · s)
  ¬tmApp₂ : ∀{t s n} → Tm n t → ¬Tm n s → ¬Tm n (t · s)
  ¬tmSucc : ∀{t n} → ¬Tm n t → ¬Tm n (Succ t)
  ¬tmRec₁ : ∀{z s t n} → ¬Tm n z → ¬Tm n (Rec z s t)
  ¬tmRec₂ : ∀{z s t n} → Tm n z → ¬Tm n s → ¬Tm n (Rec z s t)
  ¬tmRec₃ : ∀{z s t n} → Tm n z → Tm n s → ¬Tm n t → ¬Tm n (Rec z s t)

Tm≡ : ∀{t s n m} → t ≡ s → n ≡ m → Tm n t → Tm m s
Tm≡ refl refl tm = tm

¬Tm≡ : ∀{t s n m} → t ≡ s → n ≡ m → ¬Tm n t → ¬Tm m s
¬Tm≡ refl refl tm = tm

tmSuccLemma : ∀{t n} → Tm n (Succ t) → Tm n t
tmSuccLemma (tmSucc tm) = tm

liftTm : ∀{t n} m → Tm n t → Tm (n + m) t
liftTm m tmFree = tmFree
liftTm m (tmVar x) = tmVar (≤+ _ x)
liftTm m (tmLam {n = n} tm) rewrite sym (plus-succ n m) = tmLam (liftTm m tm)
liftTm m (tmApp tm tm') = tmApp (liftTm m tm) (liftTm m tm')
liftTm m tmZero = tmZero
liftTm m (tmSucc tm) = tmSucc (liftTm m tm)
liftTm m (tmRec tm tm₁ tm₂) = tmRec (liftTm m tm) (liftTm m tm₁) (liftTm m tm₂)

¬Tm-lemma : ∀{n t} → ¬Tm n t → Tm n t → ⊥
¬Tm-lemma (¬tmVar p) (tmVar q) = absurde _ _ p q
¬Tm-lemma (¬tmLam ¬tm) (tmLam tm) = ¬Tm-lemma ¬tm tm
¬Tm-lemma (¬tmApp₁ ¬tm) (tmApp tm _) = ¬Tm-lemma ¬tm tm
¬Tm-lemma (¬tmApp₂ x ¬tm) (tmApp _ tm) = ¬Tm-lemma ¬tm tm
¬Tm-lemma (¬tmSucc tm) (tmSucc tm') = ¬Tm-lemma tm tm'
¬Tm-lemma (¬tmRec₁ tm) (tmRec tm' tm'' tm''') = ¬Tm-lemma tm tm'
¬Tm-lemma (¬tmRec₂ x tm) (tmRec tm' tm'' tm''') = ¬Tm-lemma tm tm''
¬Tm-lemma (¬tmRec₃ x x₁ tm) (tmRec tm' tm'' tm''') = ¬Tm-lemma tm tm'''

decTm : ∀ n → (t : Term) → Tm n t ⊎ ¬Tm n t
decTm n (Free x) = inj₁ tmFree
decTm n (Bound x) with suc x ≤? n
decTm .(suc _) (Bound x) | yes (s≤s p) = inj₁ (tmVar p)
decTm n (Bound x) | no ¬p with qwerty _ _ ¬p
decTm n (Bound x) | no ¬p | s≤s w = inj₂ (¬tmVar w)
decTm n (Lam t) with decTm (suc n) t
decTm n (Lam t) | inj₁ x = inj₁ (tmLam x)
decTm n (Lam t) | inj₂ y = inj₂ (¬tmLam y)
decTm n (t · s) with decTm n t | decTm n s
decTm n (t · s) | inj₁ x | inj₁ x₁ = inj₁ (tmApp x x₁)
decTm n (t · s) | inj₁ x | inj₂ y = inj₂ (¬tmApp₂ x y)
decTm n (t · s) | inj₂ y | _ = inj₂ (¬tmApp₁ y)
decTm n Zero = inj₁ tmZero
decTm n (Succ t) with decTm n t
decTm n (Succ t) | inj₁ x = inj₁ (tmSucc x)
decTm n (Succ t) | inj₂ y = inj₂ (¬tmSucc y)
decTm n (Rec z s t) with decTm n z | decTm n s | decTm n t
decTm n (Rec z s t) | inj₁ x | inj₁ x₁ | inj₁ x₂ = inj₁ (tmRec x x₁ x₂)
decTm n (Rec z s t) | inj₁ x | inj₁ x₁ | inj₂ y = inj₂ (¬tmRec₃ x x₁ y)
decTm n (Rec z s t) | inj₁ x | inj₂ y | _ = inj₂ (¬tmRec₂ x y)
decTm n (Rec z s t) | inj₂ y | _ | _ = inj₂ (¬tmRec₁ y)

inj-tmApp₂ : ∀{t n s} → ¬Tm n s → ¬Tm n (t · s)
inj-tmApp₂ {t} {n} tm with decTm n t
inj-tmApp₂ tm | inj₁ x = ¬tmApp₂ x tm
inj-tmApp₂ tm | inj₂ y = ¬tmApp₁ y

inj-tmRec₂ : ∀{z n s t} → ¬Tm n s → ¬Tm n (Rec z s t)
inj-tmRec₂ {z} {n} tm with decTm n z
inj-tmRec₂ tm | inj₁ x = ¬tmRec₂ x tm
inj-tmRec₂ tm | inj₂ y = ¬tmRec₁ y

inj-tmRec₃ : ∀{z s n t} → ¬Tm n t → ¬Tm n (Rec z s t)
inj-tmRec₃ {z} {s} {n} tm with decTm n z | decTm n s
inj-tmRec₃ tm | inj₁ x | inj₁ x₁ = ¬tmRec₃ x x₁ tm
inj-tmRec₃ tm | inj₁ x | inj₂ y = ¬tmRec₂ x y
inj-tmRec₃ tm | inj₂ y | _ = ¬tmRec₁ y

¬Tm-lemma' : ∀{n t} → (Tm n t → ⊥) → ¬Tm n t
¬Tm-lemma' {t = Free x} h = ⊥-elim (h tmFree)
¬Tm-lemma' {n} {Bound x} h with n ≤? x
¬Tm-lemma' {n} {Bound x} h | yes p = ¬tmVar p
¬Tm-lemma' {zero} {Bound x} h | no ¬p = ⊥-elim (¬p z≤n)
¬Tm-lemma' {suc n} {Bound x} h | no ¬p with qwerty _ _ ¬p
¬Tm-lemma' {suc n} {Bound x} h | no ¬p | s≤s w = ⊥-elim (h (tmVar w))
¬Tm-lemma' {t = Zero} h = ⊥-elim (h tmZero)
¬Tm-lemma' {n} {Succ t} h with decTm n t
¬Tm-lemma' h | inj₁ x = ⊥-elim (h (tmSucc x))
¬Tm-lemma' h | inj₂ y = ¬tmSucc y
¬Tm-lemma' {n} {Lam t} h with decTm (suc n) t
¬Tm-lemma' h | inj₁ x = ⊥-elim (h (tmLam x))
¬Tm-lemma' h | inj₂ y = ¬tmLam y
¬Tm-lemma' {n} {t · s} h with decTm n t | decTm n s
¬Tm-lemma' h | inj₁ x | inj₁ x₁ = ⊥-elim (h (tmApp x x₁))
¬Tm-lemma' h | inj₁ x | inj₂ y = ¬tmApp₂ x y
¬Tm-lemma' h | inj₂ y | _ = ¬tmApp₁ y
¬Tm-lemma' {n} {Rec z s t} h with decTm n z | decTm n s | decTm n t
¬Tm-lemma' h | inj₁ x | inj₁ x₁ | inj₁ x₂ = ⊥-elim (h (tmRec x x₁ x₂))
¬Tm-lemma' h | inj₁ x | inj₁ x₁ | inj₂ y = ¬tmRec₃ x x₁ y
¬Tm-lemma' h | inj₁ x | inj₂ y | _ = ¬tmRec₂ x y
¬Tm-lemma' h | inj₂ y | _ | _ = ¬tmRec₁ y
