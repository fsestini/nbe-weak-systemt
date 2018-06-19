module Semantics.Completeness.Rule where

open import Syntax hiding (tmSuccLemma)
open import Data.Nat
open import Data.Maybe
open import Semantics.Domain.Domain
open import Semantics.Completeness.Type.SemTy
open import Semantics.Completeness.Type.Lemmata
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality

open SemTy
open _∈_
open ⟦_⟧≃⟦_⟧_∈tm_
open import Relation.Nullary
open import Data.Empty
open import Function

models-app : ∀{A B Γ t s} → Γ ⊧ t ∶ A => B → Γ ⊧ s ∶ A → Γ ⊧ t · s ∶ B
models-app {A} {B} ht hs ρ = tmAppLemma {A} {B} (ht ρ) (hs ρ)

models-lam : ∀{A B Γ t} → Γ # A ⊧ t ∶ B → Γ ⊧ Lam t ∶ A => B
models-lam {A} {B} ht ρ = tmLamLemma {A} {B} (λ x → ht (cCons (cWk ρ) (wit x)))

models-succ : ∀{Γ t} → Γ ⊧ t ∶ N → Γ ⊧ Succ t ∶ N
models-succ ht ρ = tmSuccLemma (ht ρ)

models-rec : ∀{A Γ z s t} 
           → Γ ⊧ z ∶ A 
           → Γ ⊧ s ∶ N => A => A 
           → Γ ⊧ t ∶ N → Γ ⊧ Rec z s t ∶ A
models-rec {A} hz hs ht ρ = tmRecLemma {A} (hz ρ) (hs ρ) (ht ρ)           

models-var : ∀{A Γ n} → Γ [ n ]↦ A → Γ ⊧ Bound n ∶ A
models-var () cId
models-var {A} here (cCons ρ y) = ⟨ in∈ y ∣ aux ∣ aux ⟩
  where aux = nfSelf (isNf ⟦ A ⟧ₜ y)
models-var (there x) (cCons ρ y) with models-var x ρ
models-var (there x) (cCons ρ y) | ⟨ tm ∣ e1 ∣ e2 ⟩ = ⟨ tm ∣ e1 ∣ e2 ⟩
models-var x (cWk ρ) with models-var x ρ
models-var {A} x (cWk {w = w} ρ) | ⟨ tm ∣ e1 ∣ e2 ⟩ = 
  ⟨ liftD {A} {w} tm ∣ wkEval e1 ∣ wkEval e2 ⟩

models : ∀{Θ Γ A t} → Θ ∷ Γ ⊢ t ∶ A → Γ ⊧ t ∶ A
models = model (record
  { _∷_⊧_∶_ = const _⊧_∶_
  ; M-free = λ { {A = A} _ _ → ⟨ in∈ (hasNe ⟦ A ⟧ₜ neFree) ∣ eFree ∣ eFree ⟩ }
  ; M-var = models-var
  ; M-lam = λ { {A = A} {B} → models-lam {A} {B} }
  ; M-● = λ { {A = A} {B} → models-app {A} {B} }
  ; M-zZ = const ⟨ in∈ natZ ∣ eZero ∣ eZero ⟩
  ; M-sS = models-succ
  ; M-rec =  λ { {A = A} → models-rec {A} }
  })

--------------------------------------------------------------------------------
-- Normalization function

std : (Γ : Ctxt) → idsub Γ ∈ₛ ⟦ Γ ⟧ₛ
std ◇ = cId
std (Γ # A) = cCons (cWk (std Γ)) (SemTy.hasNe ⟦ A ⟧ₜ neBound)

nf : ∀{Θ Γ A t} → Θ ∷ Γ ⊢ t ∶ A → Term
nf {Θ} {Γ} td = d aux where aux = models td (std Γ)
