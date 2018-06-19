module Semantics.Completeness.Equality where

open import Syntax hiding (tmSuccLemma)
open import Data.Nat
open import Data.Maybe
open import Semantics.Domain.Domain
open import Semantics.Completeness.Type.SemTy
open import Semantics.Completeness.Type.Lemmata
open import Semantics.Completeness.Rule
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality

open _∈_
open SemTy
open ⟦_⟧≃⟦_⟧_∈tm_

models-ξ : ∀{A B Γ t s} → Γ # A ⊧ t ≃ s ∶ B → Γ ⊧ Lam t ≃ Lam s ∶ A => B
models-ξ {A} {B} h ρ = tmLamLemma {A} {B} λ x → h (cCons (cWk ρ) (wit x))

models⟶ : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ⟶ s ∶ A → Γ ⊧ t ≃ s ∶ A
models⟶ (⟶β {A = A} {B = B} t s) ρ =
  tmβLemma {A = A} {B} (models (wkTerm (lam t)) ρ) (models (wkTerm s) ρ)
           (tyClosed t) (tyClosed s)
models⟶ (⟶recZ {A = A} x x₁) ρ =
  tmRecZLemma {A = A} (models (wkTerm x) ρ) (models (wkTerm x₁) ρ)
    (tyClosed x) (tyClosed x₁)
models⟶ {A = A} (⟶recS z s n) ρ =
  tmRecSLemma {A = A}
    (models (wkTerm z) ρ) (models (wkTerm s) ρ) (models (wkTerm n) ρ)
    (tyClosed z) (tyClosed s) (tyClosed n)
models⟶ (⟶ξ {A = A} {B = B} eq) = models-ξ {A} {B} (models⟶ eq)
models⟶ (⟶compSucc eq) ρ = tmSuccLemma (models⟶ eq ρ)
models⟶ (⟶compApp₁ {A = A} {B} red x) ρ =
  tmAppLemma {A} {B} (models⟶ red ρ) (models x ρ)
models⟶ (⟶compApp₂ {A = A} {B} x red) ρ =
  tmAppLemma {A} {B} (models x ρ) (models⟶ red ρ)
models⟶ (⟶compRec₁ {A = A} red x y) ρ =
  tmRecLemma {A} (models⟶ red ρ) (models x ρ) (models y ρ)
models⟶ (⟶compRec₂ {A = A} x red y) ρ =
  tmRecLemma {A} (models x ρ) (models⟶ red ρ) (models y ρ)
models⟶ (⟶compRec₃ {A = A} x y red) ρ =
  tmRecLemma {A} (models x ρ) (models y ρ) (models⟶ red ρ)

models∼ : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ∼ s ∶ A → Γ ⊧ t ≃ s ∶ A
models∼ (~⟶ x) = models⟶ x
models∼ (∼refl x) ρ = models x ρ
models∼ (∼symm eq) ρ = ⟨ ∈tm ih ∣ ↘tm2 ih ∣ ↘tm1 ih ⟩ where ih = models∼ eq ρ
models∼ (∼trans eq eq') ρ =
  ⟨ ∈tm ih ∣ ↘tm1 ih ∣ ≡Eval refl (Eval-fun (↘tm1 ih') (↘tm2 ih)) (↘tm2 ih') ⟩
  where ih = models∼ eq ρ ; ih' = models∼ eq' ρ

completeness : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ∼ s ∶ A
             → (td : Θ ∷ Γ ⊢ t ∶ A) → (sd : Θ ∷ Γ ⊢ s ∶ A)
             → nf td ≡ nf sd
completeness {Θ} {Γ} eq td sd =
  trans (Eval-fun (↘tm1 aux-t) (↘tm1 aux)) (Eval-fun (↘tm2 aux) (↘tm2 aux-s))
  where aux-t = models td (std Γ) ; aux-s = models sd (std Γ)
        aux = models∼ eq (std Γ)
