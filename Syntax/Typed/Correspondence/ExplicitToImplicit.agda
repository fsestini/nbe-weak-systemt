module Syntax.Typed.Correspondence.ExplicitToImplicit where

open import Syntax.Raw
open import Syntax.Typed.Typed
open import Data.Nat
open import Relation.Nullary
open import Data.Empty
open import Syntax.Typed.Equality.Equality
open import Syntax.Typed.Target
open import Relation.Binary.PropositionalEquality hiding ([_])

null-msub' : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ∶ A → t ≡ msub t [ clen Θ ↦ s ]
null-msub' t = sym (null-msub (metaTyClosed t))

record Factor (Θ : Ctxtₗ) (Γ : Ctxt) (t s : Term) (A : Ty) : Set where
  field
    {C a b} : Term
    {ty}    : Ty
    cder    : Θ # ty ∷ Γ ⊢ C ∶ A
    teq     : t ≡ msub C [ clen Θ ↦ a ]
    seq     : s ≡ msub C [ clen Θ ↦ b ]
    tyeq    : Θ ⊢ a ∼ b ∶ ty

factor : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ⟶ s ∶ A → Factor Θ Γ t s A
factor {Θ} (⟶β {B = B} {t} {s} td sd) =
  record
    { cder = free here ; teq = sym (sngl-msub (clen Θ))
    ; seq = sym (sngl-msub (clen Θ)) ; tyeq = ∼β td sd
    }
factor {Θ} (⟶recZ {A = A} {z} {s} zd sd) =
  record
    { cder = free here ; teq = sym (sngl-msub (clen Θ))
    ; seq = sym (sngl-msub (clen Θ)) ; tyeq = ∼recZ zd sd
    }
factor {Θ} (⟶recS {A = A} {z} {s} {n} zd sd nd) =
  record
    { cder = free here ; teq = sym (sngl-msub (clen Θ))
    ; seq = sym (sngl-msub (clen Θ)) ; tyeq = ∼recS zd sd nd
    }
factor (⟶ξ td) with factor td
factor (⟶ξ td) |
  record { cder = cder ; teq = teq ; seq = seq ; tyeq = tyeq } =
  record
    { cder = lam cder ; teq = cong Lam teq ; seq = cong Lam seq ; tyeq = tyeq }
factor (⟶compSucc td) with factor td
factor (⟶compSucc td) |
  record { cder = cder ; teq = teq ; seq = seq ; tyeq = tyeq } =
  record
    { cder = sS cder ; teq = cong Succ teq ; seq = cong Succ seq ; tyeq = tyeq }
factor (⟶compApp₁ rx sd) with factor rx
factor (⟶compApp₁ {s = s} rx sd) |
  record { cder = cder ; teq = teq ; seq = seq ; tyeq = tyeq } =
  record
    { cder = cder ● wkMeta (◇ # _) sd ; tyeq = tyeq
    ; teq = cong₂ _·_ teq (null-msub' sd) ; seq = cong₂ _·_ seq (null-msub' sd) }
factor (⟶compApp₂ rd rx) with factor rx
factor (⟶compApp₂ {r = r} rd rx) |
  record { cder = cder ; teq = teq ; seq = seq ; tyeq = tyeq } =
  record
    { cder = wkMeta (◇ # _) rd ● cder ; tyeq = tyeq
    ; teq = cong₂ _·_ (null-msub' rd) teq ; seq = cong₂ _·_ (null-msub' rd) seq }
factor (⟶compRec₁ rx sd nd) with factor rx
factor (⟶compRec₁ {s = s} {n = n} rx sd nd) |
  record { cder = cder ; teq = teq ; seq = seq ; tyeq = tyeq } =
  record
    { cder = rec cder (wkMeta (◇ # _) sd) (wkMeta (◇ # _) nd)
    ; teq = cong₃ Rec teq (null-msub' sd) (null-msub' nd)
    ; seq = cong₃ Rec seq (null-msub' sd) (null-msub' nd)
    ; tyeq = tyeq }
factor (⟶compRec₂ zd rx nd) with factor rx
factor (⟶compRec₂ {z = z} {n = n} zd rx nd) |
  record { cder = cder ; teq = teq ; seq = seq ; tyeq = tyeq } =
  record
    { cder = rec (wkMeta (◇ # _) zd) cder (wkMeta (◇ # _) nd)
    ; teq = cong₃ Rec (null-msub' zd) teq (null-msub' nd)
    ; seq = cong₃ Rec (null-msub' zd) seq (null-msub' nd)
    ; tyeq = tyeq }
factor (⟶compRec₃ zd sd rx) with factor rx
factor (⟶compRec₃ {z = z} {s = s} zd sd rx) |
  record { cder = cder ; teq = teq ; seq = seq ; tyeq = tyeq } =
  record
    { cder = rec (wkMeta (◇ # _) zd) (wkMeta (◇ # _) sd) cder
    ; teq = cong₃ Rec (null-msub' zd) (null-msub' sd) teq
    ; seq = cong₃ Rec (null-msub' zd) (null-msub' sd) seq
    ; tyeq = tyeq }

auxlemma' : ∀{A} Θ Δ
          → Θ # A ++ Δ ⊢ₛ [ clen Θ ↦ Free (clen Θ) ]
                  ∼  [ clen Θ ↦ Free (clen Θ) ] ∶ Θ # A
auxlemma' ◇ Δ = ∼cons ∼empty (∼refl (free (++ₗ-lemma Δ here)))
auxlemma' {A} (Θ # B) Δ =
  ∼cons (≡∼ₛ (auxlemma' Θ (◇ # A ++ Δ)) (swap++ {A} (Θ # B) Δ))
    (∼refl (free (++ₗ-lemma Δ here)))
  where
    ≡∼ₛ : ∀{Θ Θ' σ τ Δ} → Θ' ⊢ₛ σ ∼ τ ∶ Δ → Θ ≡ Θ' → Θ ⊢ₛ σ ∼ τ ∶ Δ
    ≡∼ₛ eq refl = eq

auxlemma : ∀{A a b} Θ
         → Θ ⊢ a ∼ b ∶ A
         → Θ ⊢ₛ [ clen Θ ↦ a ] ∼ [ clen Θ ↦ b ] ∶ Θ # A
auxlemma ◇ eq = ∼cons ∼empty eq
auxlemma (Θ # x) eq = ∼cons (auxlemma' Θ ◇) eq

convert∼ : ∀{Θ A t s} → Θ ∷ ◇ ⊢ t ∼ s ∶ A → Θ ⊢ t ∼ s ∶ A
convert∼ (∼refl x) = ∼refl x
convert∼ (∼symm eq) = ∼symm (convert∼ eq)
convert∼ (∼trans eq eq₁) = ∼trans (convert∼ eq) (convert∼ eq₁)
convert∼ (~⟶ x) with factor x
convert∼ (~⟶ x) |
  record { cder = cder ; teq = teq ; seq = seq ; tyeq = tyeq }
  rewrite teq | seq = ∼sub cder (auxlemma _ tyeq)
