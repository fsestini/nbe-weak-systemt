module Syntax.Raw.Substitution where

open import Utils
open import Function
open import Syntax.Raw.Term
open import Syntax.Raw.Renaming public
open import Syntax.Raw.Context
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat

data Subst : Set where
  Id  : Subst
  _·_ : Subst → Wk → Subst
  _,_ : Subst → Term → Subst
infixl 7 _,_

sub-var : ℕ → Subst → Term
sub-var x Id = Bound x
sub-var x (σ · w) = wk (sub-var x σ) w
sub-var zero (σ , t) = t
sub-var (suc x) (σ , t) = sub-var x σ

shift : ℕ → Subst → Subst
shift zero σ = σ
shift (suc n) σ = shift n σ · Up Id , Bound 0

sh : Subst → Subst
sh σ = shift 1 σ

sub : Term → Subst → Term
sub (Free x) σ = Free x
sub (Bound x) σ = sub-var x σ
sub (Lam t) σ = Lam (sub t (sh σ))
sub (t · s) σ = sub t σ · sub s σ
sub Zero σ = Zero
sub (Succ t) σ = Succ (sub t σ)
sub (Rec z s t) σ = Rec (sub z σ) (sub s σ) (sub t σ)

_[_] : Term → Term → Term
t [ s ] = sub t (Id , s)

--------------------------------------------------------------------------------
-- Equality of substitutions

private
  infix 4 _≈_
  _≈_ : Subst → Subst → Set
  σ ≈ τ = (x : ℕ) → sub-var x σ ≡ sub-var x τ

  eq-shift' : ∀{σ τ} → σ ≈ τ → ∀ n → shift n σ ≈ shift n τ
  eq-shift' eq zero x = eq x
  eq-shift' eq (suc n) zero = refl
  eq-shift' eq (suc n) (suc x) = cong (λ x₁ → wk x₁ (Up Id)) (eq-shift' eq n x)

  eq-sub' : ∀{σ τ} → σ ≈ τ → ∀ t → sub t σ ≡ sub t τ
  eq-sub' eq (Free x) = refl
  eq-sub' eq (Bound x) = eq x
  eq-sub' eq (Lam t) = cong Lam (eq-sub' (eq-shift' eq 1) t)
  eq-sub' eq (t · s) = cong₂ _·_ (eq-sub' eq t) (eq-sub' eq s)
  eq-sub' eq Zero = refl
  eq-sub' eq (Succ t) = cong Succ (eq-sub' eq t)
  eq-sub' eq (Rec z s t) = cong₃ Rec (eq-sub' eq z) (eq-sub' eq s) (eq-sub' eq t)

-- Two substitutions are equal if they are point-wise equal when seen as
-- functions from variables to terms.
infix 4 _≈ˢ_
record _≈ˢ_ (σ τ : Subst) : Set where
  constructor ≈ˢin
  field ≈ˢ-meaning : σ ≈ τ
open _≈ˢ_

reflˢ : ∀{σ} → σ ≈ˢ σ
reflˢ = ≈ˢin (λ x → refl)

symmˢ : ∀{σ τ} → σ ≈ˢ τ → τ ≈ˢ σ
symmˢ (≈ˢin x) = ≈ˢin (λ x₁ → sym (x x₁))

transˢ : ∀{σ τ ρ} → σ ≈ˢ τ → τ ≈ˢ ρ → σ ≈ˢ ρ
transˢ (≈ˢin x) (≈ˢin x₁) = ≈ˢin (λ x₂ → trans (x x₂) (x₁ x₂))

eq-shift : ∀{σ τ} → σ ≈ˢ τ → ∀ n → shift n σ ≈ˢ shift n τ
eq-shift (≈ˢin x) n = ≈ˢin (eq-shift' x n)

consˢ : ∀{σ τ s} → σ ≈ˢ τ → (σ , s) ≈ˢ (τ , s)
consˢ (≈ˢin eq) = ≈ˢin λ { zero → refl ; (suc x) → eq x }

eq-sub : ∀{σ τ} → σ ≈ˢ τ → ∀ t → sub t σ ≡ sub t τ
eq-sub (≈ˢin eq) t = eq-sub' eq t

eq-dot : ∀{σ τ w} → σ ≈ˢ τ → (σ · w) ≈ˢ (τ · w)
eq-dot {w = w} (≈ˢin eq) = ≈ˢin (λ x → cong (flip wk w) (eq x))

eq-dot' : ∀{σ w w'} → w ≈ʷ w' → (σ · w) ≈ˢ (σ · w')
eq-dot' weq = ≈ˢin (λ x → eq-wk weq _)

id-eq-lemma : ∀ n → Id ≈ˢ (shift n Id)
id-eq-lemma = ≈ˢin ∘ id-eq-lemma'
  where id-eq-lemma' : ∀ n → Id ≈ (shift n Id)
        id-eq-lemma' zero x = refl
        id-eq-lemma' (suc n) zero = refl
        id-eq-lemma' (suc n) (suc x) = cong (λ z → wk z (Up Id)) (id-eq-lemma' n x)

id-sub : ∀ t → sub t Id ≡ t
id-sub (Free x) = refl
id-sub (Bound x) = refl
id-sub (Lam t) =
  cong Lam (trans (eq-sub (symmˢ {Id} {sh Id} (id-eq-lemma 1)) t) (id-sub t))
id-sub (t · s) = cong₂ _·_ (id-sub t) (id-sub s)
id-sub Zero = refl
id-sub (Succ t) = cong Succ (id-sub t)
id-sub (Rec z s t) = cong₃ Rec (id-sub z) (id-sub s) (id-sub t)

id-sub' : ∀ {n} t → sub t (shift n Id) ≡ t
id-sub' {n} t = sym (trans (sym (id-sub t)) (eq-sub (id-eq-lemma n) t))

sub-id-L : ∀{σ} → σ · Id ≈ˢ σ
sub-id-L {σ} = ≈ˢin sub-id-L'
  where sub-id-L' : σ · Id ≈ σ
        sub-id-L' x = id-wk 0 (sub-var x σ)

sh-skip : ∀{σ w} → sh σ · Skip w ≈ˢ sh (σ · w)
sh-skip {σ} {w} = ≈ˢin (λ { zero → refl
  ; (suc x) → trans (wk-comp (Up Id) (Skip w) (sub-var x σ))
             (trans (eq-wk (eq-up {Id ·ʷ w} {w} (idw-L w)) (sub-var x σ))
                    (sym (wk-comp w (Up Id) (sub-var x σ)))) })

subst-lift-sw : ∀ {w σ} t → sub t (sh σ · Skip w) ≡ sub t (sh (σ · w))
subst-lift-sw {w} {σ} t = eq-sub sh-skip t

wk-subst : ∀{w σ} t → wk (sub t σ) w ≡ sub t (σ · w)
wk-subst (Free x) = refl
wk-subst (Bound x) = refl
wk-subst (Lam t) = cong Lam (trans (wk-subst t) (subst-lift-sw t))
wk-subst (t · s) = cong₂ _·_ (wk-subst t) (wk-subst s)
wk-subst Zero = refl
wk-subst (Succ t) = cong Succ (wk-subst t)
wk-subst (Rec z s t) = cong₃ Rec (wk-subst z) (wk-subst s) (wk-subst t)

--------------------------------------------------------------------------------
-- Left composition of a weakening with a substitution
_ʷ·_ : Wk → Subst → Subst
w ʷ· Id = Id · w
w ʷ· (σ · w') = (w ʷ· σ) · w'
Id ʷ· (σ , t) = σ , t
Up w ʷ· (σ , t) = w ʷ· σ
Skip w ʷ· (σ , t) = w ʷ· σ , t

comp-swk : ∀ σ w w' → (σ · w) · w' ≈ˢ σ · (w ·ʷ w')
comp-swk σ w w' = ≈ˢin (λ x → wk-comp w w' (sub-var x σ))

subst-lift-ws : ∀{w σ} t → sub t (Skip w ʷ· sh σ) ≡ sub t (sh (w ʷ· σ))
subst-lift-ws = eq-sub (≈ˢin λ { zero → refl ; (suc x) → refl })

subst-wk-var : ∀ w σ x → sub-var (wk-var x w) σ ≡ sub-var x (w ʷ· σ)
subst-wk-var w Id x = refl
subst-wk-var w (σ · w') x = cong (flip wk w') (subst-wk-var w σ x)
subst-wk-var Id (σ , t) x = refl
subst-wk-var (Up w) (σ , t) x = subst-wk-var w σ x
subst-wk-var (Skip w) (σ , t) zero = refl
subst-wk-var (Skip w) (σ , t) (suc x) = subst-wk-var w σ x

subst-wk : ∀{w σ} t → sub (wk t w) σ ≡ sub t (w ʷ· σ)
subst-wk (Free x) = refl
subst-wk {w} {σ} (Bound x) = subst-wk-var w σ x
subst-wk {w} {σ} (Lam t) =
  cong Lam (trans (subst-wk t) (subst-lift-ws {w} {σ} t))
subst-wk {w} {σ} (t · s) = cong₂ _·_ (subst-wk t) (subst-wk s)
subst-wk Zero = refl
subst-wk (Succ t) = cong Succ (subst-wk t)
subst-wk {w} {σ} (Rec z s t) = cong₃ Rec (subst-wk z) (subst-wk s) (subst-wk t)

--------------------------------------------------------------------------------
-- Composition of substitutions
_·ˢ_ : Subst → Subst → Subst
σ ·ˢ Id = σ
σ ·ˢ (τ · w) = (σ ·ˢ τ) · w
Id ·ˢ (τ , x) = τ , x
(σ · w) ·ˢ (τ , t) = σ ·ˢ (w ʷ· (τ , t))
(σ , t) ·ˢ (τ , s) = (σ ·ˢ (τ , s)) , sub t (τ , s)

id-wk-sub-L : ∀ σ → (Id ʷ· σ) ≈ˢ σ
id-wk-sub-L σ = ≈ˢin (id-wk-sub-L' σ)
  where id-wk-sub-L' : ∀ σ → (Id ʷ· σ) ≈ σ
        id-wk-sub-L' Id x = refl
        id-wk-sub-L' (σ · w) x = cong (flip wk w) (id-wk-sub-L' σ x)
        id-wk-sub-L' (σ , t) x = refl

id-wk-comp : ∀ σ τ → (σ ·ˢ (Id ʷ· τ)) ≈ˢ (σ ·ˢ τ)
id-wk-comp σ τ = ≈ˢin (id-wk-comp' σ τ)
  where id-wk-comp' : ∀ σ τ → (σ ·ˢ (Id ʷ· τ)) ≈ (σ ·ˢ τ)
        id-wk-comp' σ Id x = id-wk 0 (sub-var x σ)
        id-wk-comp' σ (τ · w) x = cong (flip wk w) (id-wk-comp' σ τ x)
        id-wk-comp' σ (τ , t) x = refl

sub-comp-lift : ∀{σ τ} → (sh σ ·ˢ sh τ) ≈ˢ sh (σ ·ˢ τ)
sub-comp-lift {σ} {τ} =
  ≈ˢin (λ { zero → refl
          ; (suc x) → cong (flip wk (Up Id)) (≈ˢ-meaning (id-wk-comp σ τ) x) })

sub-comp-var : ∀ σ τ x → sub (sub-var x σ) τ ≡ sub-var x (σ ·ˢ τ)
sub-comp-var σ Id x = id-sub (sub-var x σ)
sub-comp-var σ (τ · w) x =
  trans (sym (wk-subst (sub-var x σ))) (cong (flip wk w) (sub-comp-var σ τ x))
sub-comp-var Id (τ , t) x = refl
sub-comp-var (σ · w) (τ , t) x =
  trans (subst-wk {w} {τ , t} (sub-var x σ)) (sub-comp-var σ (w ʷ· (τ , t)) x)
sub-comp-var (σ , t) (τ , s) zero = refl
sub-comp-var (σ , t) (τ , s) (suc x) = sub-comp-var σ (τ , s) x

sub-comp : ∀{σ τ} t → sub (sub t σ) τ ≡ sub t (σ ·ˢ τ)
sub-comp (Free x) = refl
sub-comp {σ} {τ} (Bound x) = sub-comp-var σ τ x
sub-comp {σ} {τ} (Lam t) =
  cong Lam (trans (sub-comp t) (eq-sub (sub-comp-lift {σ} {τ}) t))
sub-comp {σ} {τ} (t · s) = cong₂ _·_ (sub-comp t) (sub-comp s)
sub-comp Zero = refl
sub-comp (Succ t) = cong Succ (sub-comp t)
sub-comp {σ} {τ} (Rec z s t) = cong₃ Rec (sub-comp z) (sub-comp s) (sub-comp t)

--------------------------------------------------------------------------------
-- Other properties

id-comp-L : ∀ σ → Id ·ˢ σ ≈ˢ σ
id-comp-L σ = ≈ˢin (λ x → sym (sub-comp-var Id σ x))

sub-comp-R : ∀ {t} σ τ → (σ , t) ·ˢ τ ≈ˢ (σ ·ˢ τ , sub t τ)
sub-comp-R {t} σ τ = ≈ˢin (λ {
    zero → sym (sub-comp-var (σ , t) τ 0)
  ; (suc x) → trans (sym (sub-comp-var (σ , t) τ (suc x))) (sub-comp-var σ τ x) })

sgl-comp : ∀{σ s} → sh σ ·ˢ (Id , s) ≈ˢ (σ , s)
sgl-comp {σ} = ≈ˢin (λ { zero → refl ; (suc x) → id-wk 0 (sub-var x σ) })

singleton-comp : ∀ {σ s} t → sub (sub t (sh σ)) (Id , s) ≡ sub t (σ , s)
singleton-comp {σ} {s} t =
  trans (sub-comp {sh σ} {Id , s} t) (eq-sub (consˢ {s = s} (sub-id-L {σ})) t)

sub-var-cover-lemma : ∀{s} n m x
                    → x ≤ m + n → Sz n s
                    → Sz (m + n) (sub-var x (shift m (Id , s)))
sub-var-cover-lemma n zero zero p tm = tm
sub-var-cover-lemma .(suc _) zero (suc x) (s≤s p) tm = tmVar p
sub-var-cover-lemma n (suc m) zero p tm = tmVar z≤n
sub-var-cover-lemma n (suc m) (suc x) (s≤s p) tm =
  tm-wk-lemma (m + n) 0 1 (sub-var-cover-lemma n m x p tm)

sub-cover-lemma : ∀{t s} n m
                → Sz (suc (m + n)) t → Sz n s
                → Sz (m + n) (sub t (shift m (Id , s)))
sub-cover-lemma n m tmFree tms = tmFree
sub-cover-lemma n m (tmVar x₁) tms = sub-var-cover-lemma n m _ x₁ tms
sub-cover-lemma n m (tmLam tmt₁) tms =
  tmLam (sub-cover-lemma n (suc m) tmt₁ tms)
sub-cover-lemma n m (tmApp tmt₁ tmt₂) tms =
  tmApp (sub-cover-lemma n m tmt₁ tms) (sub-cover-lemma n m tmt₂ tms)
sub-cover-lemma n m (tmRec tmt₁ tmt₂ tmt₃) tms =
  tmRec (sub-cover-lemma n m tmt₁ tms) (sub-cover-lemma n m tmt₂ tms)
        (sub-cover-lemma n m tmt₃ tms)
sub-cover-lemma n m tmZero tms = tmZero
sub-cover-lemma n m (tmSucc tmt) tms = tmSucc (sub-cover-lemma n m tmt tms)

null-sub-var : ∀{σ} n x → x ≤ n → sub-var x (shift (suc n) σ) ≡ Bound x
null-sub-var zero .0 z≤n = refl
null-sub-var (suc n) zero p = refl
null-sub-var {σ} (suc n) (suc x) (s≤s p)
  rewrite null-sub-var {σ} n x p = refl

null-sub : ∀{σ t n} → Sz n t → sub t (shift n σ) ≡ t
null-sub tmFree = refl
null-sub (tmVar x) = null-sub-var _ _ x
null-sub (tmLam tm) = cong Lam (null-sub tm)
null-sub (tmApp tm tm₁) = cong₂ _·_ (null-sub tm) (null-sub tm₁)
null-sub (tmRec tm tm₁ tm₂) =
  cong₃ Rec (null-sub tm) (null-sub tm₁) (null-sub tm₂)
null-sub tmZero = refl
null-sub (tmSucc tm) = cong Succ (null-sub tm)

¬Sz-sub-var-lemma : ∀{σ} n m x
                  → ¬Sz (m + n) (wk (sub-var x (shift n σ)) (up m Id))
                  → ¬Sz (m + n) (Bound (x + m))
¬Sz-sub-var-lemma zero m zero tm rewrite plus-0 m = ¬tmVar (≤refl m)
¬Sz-sub-var-lemma zero m (suc x) tm rewrite plus-0 m = ¬tmVar (aux x m)
  where
    aux : ∀ x m → suc (x + m) ≥ m
    aux x zero = z≤n
    aux x (suc m) rewrite plus-succ x m = s≤s (aux x m)
¬Sz-sub-var-lemma (suc n) m zero (¬tmVar x) rewrite wk-var-ups 0 m = ¬tmVar x
¬Sz-sub-var-lemma {σ} (suc n) m (suc x) tm =
  ¬Sz≡ (cong Bound (plus-succ x m)) (sym (plus-succ m n))
    (¬Sz-sub-var-lemma {σ} n (suc m) x (¬Sz≡ aux (plus-succ m n) tm))
  where
    aux = trans (wk-comp (Up Id) (up m Id) (sub-var x (shift n σ)))
                (eq-wk {Up Id ·ʷ up m Id} {up (suc m) Id} (ups-comp 1 m) _)

¬Sz-sub-lemma : ∀{t σ} n → ¬Sz n (sub t (shift n σ)) → ¬Sz n t
¬Sz-sub-lemma {Free x} n tm = tm
¬Sz-sub-lemma {Bound x} n tm =
  ¬Sz≡ (cong Bound (plus-0 x)) refl
    (¬Sz-sub-var-lemma n 0 x (¬Sz≡ (sym (id-wk 0 _)) refl tm))
¬Sz-sub-lemma {Lam t} n (¬tmLam tm) = ¬tmLam (¬Sz-sub-lemma (suc n) tm)
¬Sz-sub-lemma {t · s} n (¬tmApp₁ tm) = ¬tmApp₁ (¬Sz-sub-lemma n tm)
¬Sz-sub-lemma {t · s} n (¬tmApp₂ x tm) = inj-tmApp₂ (¬Sz-sub-lemma n tm)
¬Sz-sub-lemma {Zero} n tm = tm
¬Sz-sub-lemma {Succ t} n (¬tmSucc tm) = ¬tmSucc (¬Sz-sub-lemma n tm)
¬Sz-sub-lemma {Rec z s t} n (¬tmRec₁ tm) = ¬tmRec₁ (¬Sz-sub-lemma n tm)
¬Sz-sub-lemma {Rec z s t} n (¬tmRec₂ x tm) = inj-tmRec₂ (¬Sz-sub-lemma n tm)
¬Sz-sub-lemma {Rec z s t} n (¬tmRec₃ x x₁ tm) = inj-tmRec₃ (¬Sz-sub-lemma n tm)

idsub : (Γ : Ctxt) → Subst
idsub Γ = shift (clen Γ) Id
