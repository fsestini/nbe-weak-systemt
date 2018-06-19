module Syntax.Typed.MetaSubstitution where

open import Data.Empty
open import Utils
open import Data.Nat
open import Syntax.Raw
open import Syntax.Typed.Typed
open import Syntax.Typed.Equality.Equality
open import Syntax.Typed.Equality.Properties
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product renaming (_,_ to _,,_)

infix 4 _⊢ₗ_∶_
data _⊢ₗ_∶_ : Ctxtₗ → MetaSubst → Ctxtₗ → Set where
  ⊢⟨⟩   : ∀{Θ} → Θ ⊢ₗ ⟨⟩ ∶ ◇
  ⊢Cons : ∀{Θ ∇ A t σ}
        → Θ ⊢ₗ σ ∶ ∇
        → Θ ∷ ◇ ⊢ t ∶ A
        → Θ ⊢ₗ σ , t ∶ ∇ # A

infix 4 _⊢ₗ_∼_∶_
data _⊢ₗ_∼_∶_ : Ctxtₗ → MetaSubst → MetaSubst → Ctxtₗ → Set where
  ⊢⟨⟩   : ∀{Θ} → Θ ⊢ₗ ⟨⟩ ∼ ⟨⟩ ∶ ◇
  ⊢Cons : ∀{Θ ∇ A t s σ τ}
        → Θ ∷ ◇ ⊢ t ∼ s ∶ A
        → Θ ⊢ₗ σ ∼ τ ∶ ∇
        → Θ ⊢ₗ σ , t ∼ τ , s ∶ ∇ # A

data Viewₗ↦ : {Γ : Ctxtₗ} → {n : ℕ} → {A : Ty} → {σ : MetaSubst}
            → Γ [ n ]ₗ↦ A → Dec (n ≡ msLen σ) → Set where
  vHere : ∀{Γ σ A} → (x : clen Γ ≡ msLen σ) → Viewₗ↦ (here {Γ} {A}) (yes x)
  vThere : ∀{Γ σ A B n}
         → (p : ¬ n ≡ msLen σ)
         → (x : Γ [ n ]ₗ↦ A) → Viewₗ↦ (there {Γ} {A} {B} x) (no p)

msLenLemma : ∀{Θ Δ σ} → Θ ⊢ₗ σ ∶ Δ → clen Δ ≡ msLen σ
msLenLemma ⊢⟨⟩ = refl
msLenLemma (⊢Cons s x) = cong suc (msLenLemma s)

mssLenLemma : ∀{Θ σ τ Δ} → Θ ⊢ₗ σ ∼ τ ∶ Δ → clen Δ ≡ msLen σ × clen Δ ≡ msLen τ
mssLenLemma ⊢⟨⟩ = refl ,, refl
mssLenLemma (⊢Cons x eq) =
  cong suc (proj₁ (mssLenLemma eq)) ,, cong suc (proj₂ (mssLenLemma eq))

mssLenLemma' : ∀{Θ σ τ Δ} → Θ ⊢ₗ σ ∼ τ ∶ Δ → msLen σ ≡ msLen τ
mssLenLemma' eq = trans (sym (proj₁ (mssLenLemma eq))) (proj₂ (mssLenLemma eq))

≤≡ : ∀{x y z} → x ≤ y → y ≡ z → x ≤ z
≤≡ p refl = p

viewₗ↦ : ∀{Δ σ n Θ A B}
       → (x : Δ # A [ n ]ₗ↦ B) → (p : Dec (n ≡ msLen σ))
       → Θ ⊢ₗ σ ∶ Δ → Viewₗ↦ x p
viewₗ↦ here (yes p) σ = vHere p
viewₗ↦ here (no ¬p) σ = ⊥-elim (¬p (msLenLemma σ))
viewₗ↦ (there x) (yes p) σ =
  ⊥-elim (¬lenLemma x (≤≡ (≤refl _) (trans (msLenLemma σ) (sym p))))
viewₗ↦ (there x) (no ¬p) σ = vThere ¬p x

viewₗ∼ : ∀{Δ σ τ n Θ A B}
       → (x : Δ # A [ n ]ₗ↦ B)
       → (p : Dec (n ≡ msLen σ)) → (q : Dec (n ≡ msLen τ))
       → Θ ⊢ₗ σ ∼ τ ∶ Δ
       → Viewₗ↦ x p × Viewₗ↦ x q
viewₗ∼ here (yes p) (yes p₁) σ = vHere p ,, vHere p₁
viewₗ∼ here (yes p) (no ¬p) σ = ⊥-elim (¬p (trans p (mssLenLemma' σ)))
viewₗ∼ here (no ¬p) (yes p) σ = ⊥-elim (¬p (proj₁ (mssLenLemma σ)))
viewₗ∼ here (no ¬p) (no ¬p₁) σ = ⊥-elim (¬p (proj₁ (mssLenLemma σ)))
viewₗ∼ (there x) (yes p) (yes p₁) σ =
  ⊥-elim (¬lenLemma x (≤≡ (≤refl _) (trans (proj₁ (mssLenLemma σ)) (sym p))))
viewₗ∼ (there x) (yes p) (no ¬p) σ = ⊥-elim (¬p (trans p (mssLenLemma' σ)))
viewₗ∼ (there x) (no ¬p) (yes p) σ = ⊥-elim (¬p (trans p (sym (mssLenLemma' σ))))
viewₗ∼ (there x) (no ¬p) (no ¬p₁) σ = vThere ¬p x ,, vThere ¬p₁ x

⊢msub : ∀{Θ ∇ Γ A t σ} → ∇ ∷ Γ ⊢ t ∶ A → Θ ⊢ₗ σ ∶ ∇
      → Θ ∷ Γ ⊢ msub t σ ∶ A
⊢msub (free ()) ⊢⟨⟩
⊢msub (free {n = n} x) (⊢Cons {σ = σ} σp x₁)
  with n ≟ msLen σ | viewₗ↦ x (n ≟ msLen σ) σp
⊢msub (free .here) (⊢Cons σp x₁) | yes p | vHere .p = wkTerm x₁
⊢msub (free .(there x)) (⊢Cons σp x₁) | no ¬p | vThere .¬p x = ⊢msub (free x) σp
⊢msub (var x) σ = var x
⊢msub (lam td) σ = lam (⊢msub td σ)
⊢msub (td ● td₁) σ = ⊢msub td σ ● ⊢msub td₁ σ
⊢msub zZ σ = zZ
⊢msub (sS td) σ = sS (⊢msub td σ)
⊢msub (rec td td₁ td₂) σ = rec (⊢msub td σ) (⊢msub td₁ σ) (⊢msub td₂ σ)

∼msub : ∀{Θ ∇ Γ A t σ τ} → ∇ ∷ Γ ⊢ t ∶ A → Θ ⊢ₗ σ ∼ τ ∶ ∇
      → Θ ∷ Γ ⊢ msub t σ ∼ msub t τ ∶ A
∼msub (free ()) ⊢⟨⟩
∼msub (free {n = n} x) (⊢Cons {σ = σ} {τ} eq seq)
  with n ≟ msLen σ | n ≟ msLen τ | viewₗ∼ x (n ≟ msLen σ) (n ≟ msLen τ) seq
∼msub (free .here) (⊢Cons eq seq) | yes p | yes p₁ | vHere _ ,, vHere _ = wk∼ eq
∼msub (free .here) (⊢Cons _ _) | yes p | no ¬p | vHere _ ,, ()
∼msub (free .(there _)) (⊢Cons _ _) | no ¬p | yes p | vThere _ x ,, ()
∼msub (free .(there x)) (⊢Cons eq seq)
  | no ¬p | no ¬p₁ | vThere .¬p x ,, vThere .¬p₁ .x = ∼msub (free x) seq
∼msub (var x) eq = ∼refl (var x)
∼msub (lam td) eq = ∼ξ (∼msub td eq)
∼msub (td ● sd) eq = ∼compApp (∼msub td eq) (∼msub sd eq)
∼msub zZ eq = ∼refl zZ
∼msub (sS td) eq = ∼compSucc (∼msub td eq)
∼msub (rec zd sd nd) eq = ∼compRec (∼msub zd eq) (∼msub sd eq) (∼msub nd eq)
