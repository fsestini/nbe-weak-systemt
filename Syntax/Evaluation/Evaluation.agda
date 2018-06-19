module Syntax.Evaluation.Evaluation where

open import Function
open import Syntax.Raw
open import Syntax.Evaluation.NormalForm
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum renaming ([_,_] to [[_,,_]])

data β-Redex : Term → Term → Set where
  βrdx : ∀{t s} → Tm 1 t → Tm 0 s → β-Redex (Lam t) s

data N-Redex : Term → Term → Term → Set where
  NrdxZ : ∀{z s} → Tm 0 z → Tm 0 s → N-Redex z s Zero
  NrdxS : ∀{z s n} → Tm 0 z → Tm 0 s → Tm 0 n → N-Redex z s (Succ n)

mutual
  infix 4 _●_↘_
  data _●_↘_ : Term → Term → Term → Set where
    ●β : ∀{t s ts} → β-Redex (Lam t) s
       → Eval sub t (Id , s) ↘ ts → Lam t ● s ↘ ts
    ●Ne : ∀{t s} → Ne (t · s) → t ● s ↘ t · s

  data Rec_·_·_↘_ : Term → Term → Term → Term → Set where
    rZ : ∀{z s} → N-Redex z s Zero → Rec z · s · Zero ↘ z
    rS : ∀{z s n a b f} → N-Redex z s (Succ n)
       → Rec z · s · n ↘ a → s ● n ↘ f → f ● a ↘ b
       → Rec z · s · (Succ n) ↘ b
    rNe : ∀{z s n} → Ne (Rec z s n) → Rec z · s · n ↘ Rec z s n

  data Eval_↘_ : Term → Term → Set where
    eBound : ∀{x} → Eval Bound x ↘ Bound x
    eFree  : ∀{x} → Eval Free x ↘ Free x
    eZero  : Eval Zero ↘ Zero
    eSucc  : ∀{t t'} → Eval t ↘ t' → Eval Succ t ↘ Succ t'
    eLam   : ∀{t t'} → Eval t ↘ t' → Eval Lam t ↘ Lam t'
    eApp   : ∀{t s t' s' ap}
           → Eval t ↘ t' → Eval s ↘ s' → t' ● s' ↘ ap → Eval t · s ↘ ap
    eRec   : ∀{z s t z' s' t' r}
           → Eval z ↘ z' → Eval s ↘ s' → Eval t ↘ t' → Rec z' · s' · t' ↘ r
           → Eval Rec z s t ↘ r

≡App : ∀{t t' s s' a b} → t ≡ t' → s ≡ s' → a ≡ b → t ● s ↘ a → t' ● s' ↘ b
≡App refl refl refl x = x

≡Rec : ∀{z z' s s' t t' a b}
     → z ≡ z' → s ≡ s' → t ≡ t' → a ≡ b
     → Rec z · s · t ↘ a → Rec z' · s' · t' ↘ b
≡Rec refl refl refl refl x = x

≡Eval : ∀{t t' a b} → t ≡ t' → a ≡ b → Eval t ↘ a → Eval t' ↘ b
≡Eval refl refl x = x

NeApp¬β : ∀{t s} → Ne (t · s) → β-Redex t s → ⊥
NeApp¬β (neApp () x x₁ x₂) (βrdx x₃ x₄)
NeApp¬β (neApp₁ x x₁ x₂) (βrdx x₃ x₄) = ¬Tm-lemma x₂ (tmLam x₃)
NeApp¬β (neApp₂ x x₁ x₂ x₃) (βrdx x₄ x₅) = ¬Tm-lemma x₃ x₅

NeRec¬N : ∀{z s n} → Ne (Rec z s n) → N-Redex z s n → ⊥
NeRec¬N (neRec x x₁ () x₂ x₃ x₄) (NrdxZ x₅ x₆)
NeRec¬N (neRec x x₁ () x₂ x₃ x₄) (NrdxS x₅ x₆ x₇)
NeRec¬N (neRec₁ x x₁ x₂ x₃) (NrdxZ x₄ x₅) = ¬Tm-lemma x₃ x₄
NeRec¬N (neRec₁ x x₁ x₂ x₃) (NrdxS x₄ x₅ x₆) = ¬Tm-lemma x₃ x₄
NeRec¬N (neRec₂ x x₁ x₂ x₃ x₄) (NrdxZ x₅ x₆) = ¬Tm-lemma x₄ x₆
NeRec¬N (neRec₂ x x₁ x₂ x₃ x₄) (NrdxS x₅ x₆ x₇) = ¬Tm-lemma x₄ x₆
NeRec¬N (neRec₃ x x₁ x₂ x₃ x₄ ()) (NrdxZ x₆ x₇)
NeRec¬N (neRec₃ x x₁ x₂ x₃ x₄ (¬tmSucc x₅)) (NrdxS x₆ x₇ x₈) = ¬Tm-lemma x₅ x₈

decβ-Redex : ∀{t s} → Nf (Lam t) → Nf s
           → β-Redex (Lam t) s ⊎ Ne (Lam t · s)
decβ-Redex {t} {s} nfl nfs with decTm 1 t | decTm 0 s
decβ-Redex {t} {s} nfl nfs | inj₁ x | inj₁ x₁ = inj₁ (βrdx x x₁)
decβ-Redex {t} {s} nfl nfs | inj₁ x | inj₂ y = inj₂ (neApp₂ nfl nfs (tmLam x) y)
decβ-Redex {t} {s} nfl nfs | inj₂ y | _ = inj₂ (neApp₁ nfl nfs (¬tmLam y))

NeLamLemma : ∀{t d σ} → Nf t → Eval sub t σ ↘ Lam d
           → (Σ Term λ d' → t ≡ Lam d') ⊎ (Ne t)
NeLamLemma (nfLam nf) (eLam e) = inj₁ (_ ,, refl)
NeLamLemma nfZero ()
NeLamLemma (nfSucc nf) ()
NeLamLemma (nfNe x) e = inj₂ x

decβ-Redex' : ∀{t s} → Nf t → Nf s
            → (Σ Term λ d → t ≡ Lam d) ⊎ (Ne t)
            → (β-Redex t s × (Σ Term λ d → t ≡ Lam d)) ⊎ Ne (t · s)
decβ-Redex' et es (inj₁ (_ ,, p)) rewrite p =
  [[ (λ x → inj₁ (x ,, (_ ,, refl))) ,, (λ x → inj₂ x) ]] (decβ-Redex et es)
decβ-Redex' et es (inj₂ y) = inj₂ (inj-neApp y es)

β-Redex-Tm-t : ∀{t s} → β-Redex t s → Tm 0 t
β-Redex-Tm-t (βrdx x _) = tmLam x

β-Redex-Tm-Lam-t : ∀{t s} → β-Redex (Lam t) s → Tm 1 t
β-Redex-Tm-Lam-t (βrdx x _) = x

β-Redex-Tm-s : ∀{t s} → β-Redex t s → Tm 0 s
β-Redex-Tm-s (βrdx x x₁) = x₁

Lam-inj : ∀{t t'} → Lam t ≡ Lam t' → t ≡ t'
Lam-inj refl = refl

N-Redex-Tm : ∀{z s t} → N-Redex z s t → Tm 0 (Rec z s t)
N-Redex-Tm (NrdxZ x x₁) = tmRec x x₁ tmZero
N-Redex-Tm (NrdxS x x₁ x₂) = tmRec x x₁ (tmSucc x₂)

N-Redex-Tm-z : ∀{z s t} → N-Redex z s t → Tm 0 z
N-Redex-Tm-z (NrdxZ x₁ x₂) = x₁
N-Redex-Tm-z (NrdxS x₁ x₂ x₃) = x₁

N-Redex-Tm-s : ∀{z s t} → N-Redex z s t → Tm 0 s
N-Redex-Tm-s (NrdxZ x₁ x₂) = x₂
N-Redex-Tm-s (NrdxS x₁ x₂ x₃) = x₂

N-Redex-Tm-t : ∀{z s t} → N-Redex z s t → Tm 0 t
N-Redex-Tm-t (NrdxZ x₁ x₂) = tmZero
N-Redex-Tm-t (NrdxS x₁ x₂ x₃) = tmSucc x₃

NeZeroLemma : ∀{t σ} → Nf t → Eval sub t σ ↘ Zero
            → t ≡ Zero ⊎ Ne t
NeZeroLemma (nfLam nf) ()
NeZeroLemma nfZero eZero = inj₁ refl
NeZeroLemma (nfSucc nf) ()
NeZeroLemma (nfNe x) e = inj₂ x

NeSuccLemma : ∀{t a σ} → Nf t → Eval sub t σ ↘ Succ a
            → (Σ Term λ d → t ≡ Succ d) ⊎ Ne t
NeSuccLemma (nfLam nf) ()
NeSuccLemma nfZero ()
NeSuccLemma (nfSucc nf) e = inj₁ (_ ,, refl)
NeSuccLemma (nfNe x) e = inj₂ x

data N-Redex-Op : Term → Set where
  nroZ  : N-Redex-Op Zero
  nroS  : ∀{t} → Nf t → N-Redex-Op (Succ t)
  nroNe : ∀{t} → Ne t → N-Redex-Op t

NOpIsNf : ∀{t} → N-Redex-Op t → Nf t
NOpIsNf nroZ = nfZero
NOpIsNf (nroS x) = nfSucc x
NOpIsNf (nroNe x) = nfNe x

decN-Redex : ∀{z s t} → Nf z → Nf s → N-Redex-Op t
           → N-Redex z s t ⊎ Ne (Rec z s t)
decN-Redex {z} {s} {t} nfz nfs nt with decTm 0 z | decTm 0 s | decTm 0 t
decN-Redex nfz nfs nroZ | inj₁ x | inj₁ x₁ | inj₁ x₂ = inj₁ (NrdxZ x x₁)
decN-Redex nfz nfs (nroS x₃) | inj₁ x | inj₁ x₁ | inj₁ x₂ =
  inj₁ (NrdxS x x₁ (tmSuccLemma x₂))
decN-Redex nfz nfs (nroNe x₃) | inj₁ x | inj₁ x₁ | inj₁ x₂ =
  inj₂ (neRec nfz nfs x₃ x x₁ x₂)
decN-Redex nfz nfs nt | inj₁ x | inj₁ x₁ | inj₂ y =
  inj₂ (inj-neRec₃ nfz nfs (NOpIsNf nt) y)
decN-Redex nfz nfs nt | inj₁ x | inj₂ y | _ =
  inj₂ (inj-neRec₂ nfz nfs (NOpIsNf nt) y)
decN-Redex nfz nfs nt | inj₂ y | _ | _ = inj₂ (neRec₁ nfz nfs (NOpIsNf nt) y)

decN-Redex-Z : ∀{z s t} → Nf z → Nf s → Nf t → t ≡ Zero ⊎ Ne t
             → (N-Redex z s t × t ≡ Zero) ⊎ Ne (Rec z s t)
decN-Redex-Z nfz nfs nft (inj₁ x) with decN-Redex nfz nfs nroZ
decN-Redex-Z {z} {s} {t} nfz nfs nft (inj₁ x) | inj₁ p =
  inj₁ (subst (N-Redex z s) (sym x) p ,, x)
decN-Redex-Z {z} {s} {t} nfz nfs nft (inj₁ x) | inj₂ q =
  inj₂ (subst (Ne ∘ Rec z s) (sym x) q)
decN-Redex-Z nfz nfs nft (inj₂ y) = inj₂ (inj-neRec nfz nfs y)

private
  aux : ∀{t} → Σ Term (λ d → t ≡ Succ d) ⊎ Ne t → Nf t → N-Redex-Op t
  aux (inj₁ (_ ,, p)) nf with subst Nf p nf
  aux (inj₁ (_ ,, p)) nf | nfSucc w = subst N-Redex-Op (sym p) (nroS w)
  aux (inj₁ (_ ,, p)) nf | nfNe x = nroNe (subst Ne (sym p) x)
  aux (inj₂ y) nf = nroNe y

  aux' : ∀{z s t} → Σ Term (λ d → t ≡ Succ d) ⊎ Ne t → N-Redex z s t
       → Σ Term (λ d → t ≡ Succ d)
  aux' (inj₁ x₂) (NrdxZ x x₁) = x₂
  aux' (inj₂ ()) (NrdxZ x x₁)
  aux' (inj₁ x₃) (NrdxS x x₁ x₂) = x₃
  aux' (inj₂ ()) (NrdxS x x₁ x₂)

decN-Redex-S : ∀{z s t} → Nf z → Nf s → Nf t
             → (Σ Term λ d → t ≡ Succ d) ⊎ Ne t
             → (N-Redex z s t × (Σ Term λ d → t ≡ Succ d)) ⊎ Ne (Rec z s t)
decN-Redex-S nfz nfs nft p with decN-Redex nfz nfs (aux p nft)
decN-Redex-S nfz nfs nft p | inj₁ x = inj₁ (x ,, aux' p x)
decN-Redex-S nfz nfs nft p | inj₂ y = inj₂ y
