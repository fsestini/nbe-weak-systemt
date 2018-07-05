module Syntax.Evaluation.NormalForm where

open import Syntax.Raw
open import Data.Empty

mutual
  data Nf : Term → Set where
    nfLam : ∀{t} → Nf t → Nf (Lam t)
    nfZero : Nf Zero
    nfSucc : ∀{t} → Nf t → Nf (Succ t)
    nfNe   : ∀{t} → Ne t → Nf t

  data Ne : Term → Set where

    neApp : ∀{t s} → Ne t → Nf s
          → Sz 0 t → Sz 0 s → Ne (t · s)
    neApp₁ : ∀{t s} → Nf t → Nf s → ¬Sz 0 t → Ne (t · s)
    neApp₂ : ∀{t s} → Nf t → Nf s → Sz 0 t → ¬Sz 0 s → Ne (t · s)

    neRec : ∀{z s t} → Nf z → Nf s → Ne t
          → Sz 0 z → Sz 0 s → Sz 0 t → Ne (Rec z s t)
    neRec₁ : ∀{z s t} → Nf z → Nf s → Nf t → ¬Sz 0 z → Ne (Rec z s t)
    neRec₂ : ∀{z s t} → Nf z → Nf s → Nf t → Sz 0 z → ¬Sz 0 s → Ne (Rec z s t)
    neRec₃ : ∀{z s t} → Nf z → Nf s → Nf t
           → Sz 0 z → Sz 0 s → ¬Sz 0 t → Ne (Rec z s t)

    neFree : ∀{x} → Ne (Free x)
    neBound : ∀{x} → Ne (Bound x)

open import Data.Sum

inj-neApp : ∀{t s} → Ne t → Nf s → Ne (t · s)
inj-neApp {t} {s} ne nf with decSz 0 t | decSz 0 s
inj-neApp {t} {s} ne nf | inj₁ x | inj₁ x₁ = neApp ne nf x x₁
inj-neApp {t} {s} ne nf | inj₁ x | inj₂ y = neApp₂ (nfNe ne) nf x y
inj-neApp {t} {s} ne nf | inj₂ y | _ = neApp₁ (nfNe ne) nf y

inj-neApp₂ : ∀{t s} → Nf t → Nf s → ¬Sz 0 s → Ne (t · s)
inj-neApp₂ {t} {s} nft nfs tm with decSz 0 t
inj-neApp₂ nft nfs tm | inj₁ x = neApp₂ nft nfs x tm
inj-neApp₂ nft nfs tm | inj₂ y = neApp₁ nft nfs y

inj-neRec : ∀{z s t} → Nf z → Nf s → Ne t → Ne (Rec z s t)
inj-neRec {z} {s} {t} nfz nfs ne with decSz 0 z | decSz 0 s | decSz 0 t
inj-neRec nfz nfs ne | inj₁ x | inj₁ x₁ | inj₁ x₂ = neRec nfz nfs ne x x₁ x₂
inj-neRec nfz nfs ne | inj₁ x | inj₁ x₁ | inj₂ y = neRec₃ nfz nfs (nfNe ne) x x₁ y
inj-neRec nfz nfs ne | inj₁ x | inj₂ y | _ = neRec₂ nfz nfs (nfNe ne) x y
inj-neRec nfz nfs ne | inj₂ y | _ | _ = neRec₁ nfz nfs (nfNe ne) y

inj-neRec₂ : ∀{z s t} → Nf z → Nf s → Nf t → ¬Sz 0 s → Ne (Rec z s t)
inj-neRec₂ {z} nfz nfs nft tm with decSz 0 z
inj-neRec₂ nfz nfs nft tm | inj₁ x = neRec₂ nfz nfs nft x tm
inj-neRec₂ nfz nfs nft tm | inj₂ y = neRec₁ nfz nfs nft y

inj-neRec₃ : ∀{z s t} → Nf z → Nf s → Nf t → ¬Sz 0 t → Ne (Rec z s t)
inj-neRec₃ {z} {s} nfz nfs nft tm with decSz 0 z | decSz 0 s
inj-neRec₃ nfz nfs nft tm | inj₁ x | inj₁ x₁ = neRec₃ nfz nfs nft x x₁ tm
inj-neRec₃ nfz nfs nft tm | inj₁ x | inj₂ y = neRec₂ nfz nfs nft x y
inj-neRec₃ nfz nfs nft tm | inj₂ y | _ = neRec₁ nfz nfs nft y

open import Data.Nat

mutual

  neWkLemma : ∀{a w} → Ne a → Ne (wk a w)
  neWkLemma (neApp ne x y z) =
    neApp (neWkLemma ne) (nfWkLemma x) (tm-wk-0 y) (tm-wk-0 z)
  neWkLemma (neApp₁ x y z) = neApp₁ (nfWkLemma x) (nfWkLemma y) (sub¬Sz-lemma z)
  neWkLemma (neApp₂ x y z r) =
    neApp₂ (nfWkLemma x) (nfWkLemma y) (tm-wk-0 z) (sub¬Sz-lemma r)
  neWkLemma (neRec z s ne tmz tms tmt) =
    neRec (nfWkLemma z) (nfWkLemma s) (neWkLemma ne)
      (tm-wk-0 tmz) (tm-wk-0 tms) (tm-wk-0 tmt)
  neWkLemma (neRec₁ z s t tm) =
    neRec₁ (nfWkLemma z) (nfWkLemma s) (nfWkLemma t) (sub¬Sz-lemma tm)
  neWkLemma (neRec₂ z s t tm tm') =
    neRec₂ (nfWkLemma z) (nfWkLemma s) (nfWkLemma t)
      (tm-wk-0 tm) (sub¬Sz-lemma tm')
  neWkLemma (neRec₃ z s t tmz tms tmt) =
    neRec₃ (nfWkLemma z) (nfWkLemma s) (nfWkLemma t)
      (tm-wk-0 tmz) (tm-wk-0 tms) (sub¬Sz-lemma tmt)
  neWkLemma neFree = neFree
  neWkLemma neBound = neBound

  nfWkLemma : ∀{a w} → Nf a → Nf (wk a w)
  nfWkLemma (nfLam nf) = nfLam (nfWkLemma nf)
  nfWkLemma nfZero = nfZero
  nfWkLemma (nfSucc nf) = nfSucc (nfWkLemma nf)
  nfWkLemma (nfNe x) = nfNe (neWkLemma x)

data NeView : Term → Set where
  NVApp : ∀{t s} → Nf t → Nf s → NeView (t · s)
  NVRec : ∀{z s t} → Nf z → Nf s → Nf t → NeView (Rec z s t)
  NVFree : ∀{x} → NeView (Free x)
  NVBound : ∀{x} → NeView (Bound x)

neView : ∀{t} → Ne t → NeView t
neView (neApp ne x x₁ x₂) = NVApp (nfNe ne) x
neView (neApp₁ x x₁ x₂) = NVApp x x₁
neView (neApp₂ x x₁ x₂ x₃) = NVApp x x₁
neView (neRec x x₁ ne x₂ x₃ x₄) = NVRec x x₁ (nfNe ne)
neView (neRec₁ x x₁ x₂ x₃) = NVRec x x₁ x₂
neView (neRec₂ x x₁ x₂ x₃ x₄) = NVRec x x₁ x₂
neView (neRec₃ x x₁ x₂ x₃ x₄ x₅) = NVRec x x₁ x₂
neView neFree = NVFree
neView neBound = NVBound

neBeta : ∀{t s} → Ne (Lam t · s) → Sz 1 t → Sz 0 s → ⊥
neBeta (neApp () x x₁ x₂) tmt tms
neBeta (neApp₁ x x₁ x₂) tmt tms = ¬Sz-lemma x₂ (tmLam tmt)
neBeta (neApp₂ x x₁ x₂ x₃) tmt tms = ¬Sz-lemma x₃ tms
