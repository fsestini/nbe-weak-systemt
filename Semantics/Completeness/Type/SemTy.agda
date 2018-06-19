module Semantics.Completeness.Type.SemTy where

open import Data.Nat
open import Data.Product renaming (_,_ to _,,_)
open import Data.Maybe
open import Syntax
open import Semantics.Domain.Domain
open import Relation.Binary.PropositionalEquality

_∈ₜ_ : D → (D → Set) → Set
d ∈ₜ T = T d

record SemTy : Set₁ where
  field
    P : D → Set
    isNf  : ∀{a} → P a → Nf a
    hasNe : ∀{e} → Ne e → P e
open SemTy

infix 4 _∈_
record _∈_ (a : D) (A : SemTy) : Set where
  no-eta-equality
  constructor in∈
  field
    wit : a ∈ₜ P A
open _∈_

hasFree : ∀{A x} → Free x ∈ A
hasFree {A} = in∈ (hasNe A neFree)

hasBound : ∀{A x} → Bound x ∈ A
hasBound {A} = in∈ (hasNe A neBound)

infix 4 ⟦_⟧≃⟦_⟧_∈tm_
record ⟦_⟧≃⟦_⟧_∈tm_ (t t' : Term) (ρ : Subst) (T : SemTy) : Set where
  constructor ⟨_∣_∣_⟩
  field
    {d} : D
    ∈tm : d ∈ T
    ↘tm1 : t [ ρ ]↘ d
    ↘tm2 : t' [ ρ ]↘ d

record _●_∈ap_ (f a : D) (B : SemTy) : Set where
  field
    {res} : D
    ∈tm   : res ∈ B
    ↘ap  : f ● a ↘ res
open _●_∈ap_

record rec_·_·_∈r_ (z s t : D) (A : SemTy) : Set where
  field
    {res} : D
    ∈tm  : res ∈ A
    ↘rec : Rec z · s · t ↘ res
open rec_·_·_∈r_

--------------------------------------------------------------------------------

data NatP : D → Set where
  natZ  : NatP Zero
  natS  : ∀{n} → NatP n → NatP (Succ n)
  natNe : ∀{e} → Ne e → NatP e

Nat : SemTy
Nat = record { P = NatP ; isNf = is-nf ; hasNe = natNe }
  where
    is-nf : {a : Term} → NatP a → Nf a
    is-nf natZ = nfZero
    is-nf (natS nat) = nfSucc (is-nf nat)
    is-nf (natNe x) = nfNe x

FunP : SemTy → SemTy → D → Set
FunP A B f = Nf f × (∀{a w} → P A a → wk f w ● a ∈ap B)

infixr 6 _==>_
_==>_ : SemTy → SemTy → SemTy
A ==> B = record { P = FunP A B ; isNf = proj₁ ; hasNe = has-ne }
  where
    has-ne : {e : Term} → Ne e → FunP A B e
    has-ne {e} ne = nfNe ne ,, aux
      where
        aux : ∀{a w} → P A a → wk e w ● a ∈ap B
        aux pa = record { ∈tm = in∈ (hasNe B nee) ; ↘ap = ●Ne nee }
          where nee = inj-neApp (neWkLemma ne) (isNf A pa)

⟦_⟧ₜ : Ty → SemTy
⟦ N ⟧ₜ = Nat
⟦ A => Q ⟧ₜ = ⟦ A ⟧ₜ ==> ⟦ Q ⟧ₜ

liftD : ∀{A w d} → d ∈ ⟦ A ⟧ₜ → wk d w ∈ ⟦ A ⟧ₜ
liftD {N} {w} (in∈ natZ) = in∈ natZ
liftD {N} {w} (in∈ (natS p)) = in∈ (natS (wit (liftD {N} {w} (in∈ p))))
liftD {N} {w} (in∈ (natNe x)) = in∈ (natNe (neWkLemma x))
liftD {A => B} {w} {f} (in∈ (nf ,, h)) = in∈ ((nfWkLemma nf) ,, aux)
  where
    aux : ∀{a w'} → P ⟦ A ⟧ₜ a → wk (wk f w) w' ● a ∈ap ⟦ B ⟧ₜ
    aux {a} {w'} p rewrite wk-comp w w' f = h {a} {w ·ʷ w'} p

_∈ₛ_ : Subst → (Subst → Set) → Set
ρ ∈ₛ S = S ρ

data ⟦_⟧ₛ :  Ctxt → Subst → Set where
  cId   : ∀{ρ} → ⟦ ◇ ⟧ₛ ρ
  cCons : ∀{Γ A ρ d} → ρ ∈ₛ ⟦ Γ ⟧ₛ → d ∈ₜ P ⟦ A ⟧ₜ → ⟦ Γ # A ⟧ₛ (ρ , d)
  cWk   : ∀{Γ w ρ} → ρ ∈ₛ ⟦ Γ ⟧ₛ → ⟦ Γ ⟧ₛ (ρ · w)

infix 4 _⊧_≃_∶_
_⊧_≃_∶_ : Ctxt → Term → Term → Ty → Set
Γ ⊧ t ≃ t' ∶ A = ∀{ρ} → ρ ∈ₛ ⟦ Γ ⟧ₛ → ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm ⟦ A ⟧ₜ

infix 4 _⊧_∶_
_⊧_∶_ : Ctxt → Term → Ty → Set
Γ ⊧ t ∶ A = Γ ⊧ t ≃ t ∶ A
