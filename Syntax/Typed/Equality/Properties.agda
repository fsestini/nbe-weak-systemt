module Syntax.Typed.Equality.Properties where

open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)
open import Syntax.Raw
open import Syntax.Typed.Typed
open import Data.Nat
open import Relation.Nullary
open import Data.Empty
open import Syntax.Typed.Equality.Equality

⟶lemma : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ⟶ s ∶ A → Θ ∷ Γ ⊢ t ∶ A × Θ ∷ Γ ⊢ s ∶ A
⟶lemma (⟶β x x₁) = wkTerm (lam x ● x₁) ,, wkTerm (⊢sub x (⊢Cons ⊢Id x₁))
⟶lemma (⟶recZ x x₁) = wkTerm (rec x x₁ zZ) ,, wkTerm x
⟶lemma (⟶recS x x₁ x₂) =
  wkTerm (rec x x₁ (sS x₂)) ,, wkTerm (x₁ ● x₂ ● rec x x₁ x₂)
⟶lemma (⟶ξ red) = lam (proj₁ (⟶lemma red)) ,, lam (proj₂ (⟶lemma red))
⟶lemma (⟶compSucc red) = sS (proj₁ (⟶lemma red)) ,, sS (proj₂ (⟶lemma red))
⟶lemma (⟶compApp₁ red x) = proj₁ (⟶lemma red) ● x ,, proj₂ (⟶lemma red) ● x
⟶lemma (⟶compApp₂ x red) = x ● proj₁ (⟶lemma red) ,, x ● proj₂ (⟶lemma red)
⟶lemma (⟶compRec₁ red x x₁) =
  rec (proj₁ (⟶lemma red)) x x₁ ,, rec (proj₂ (⟶lemma red)) x x₁
⟶lemma (⟶compRec₂ x red x₁) =
  rec x (proj₁ (⟶lemma red)) x₁ ,, rec x (proj₂ (⟶lemma red)) x₁
⟶lemma (⟶compRec₃ x x₁ red) =
  rec x x₁ (proj₁ (⟶lemma red)) ,, rec x x₁ (proj₂ (⟶lemma red))

∼lemma : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Γ ⊢ t ∶ A × Θ ∷ Γ ⊢ s ∶ A
∼lemma (~⟶ x) = ⟶lemma x
∼lemma (∼refl x) = x ,, x
∼lemma (∼symm eq) = proj₂ (∼lemma eq) ,, proj₁ (∼lemma eq)
∼lemma (∼trans eq eq₁) = proj₁ (∼lemma eq) ,, proj₂ (∼lemma eq₁)

mutual

  sameTm⟶LR : ∀{Θ Γ Δ A t s}
              → Θ ∷ Δ ++ Γ ⊢ t ⟶ s ∶ A → Tm (clen Γ) t → Tm (clen Γ) s
  sameTm⟶LR {_} {Γ} (⟶β x x₁) (tmApp (tmLam tm) tm₁) =
    sub-cover-lemma (clen Γ) 0 tm tm₁
  sameTm⟶LR (⟶recZ x x₁) (tmRec tm tm₁ tm₂) = tm
  sameTm⟶LR (⟶recS x x₁ x₂) (tmRec tm tm₁ (tmSucc tm₂)) =
    tmApp (tmApp tm₁ tm₂) (tmRec tm tm₁ tm₂)
  sameTm⟶LR (⟶ξ eq) (tmLam tm) = tmLam (sameTm⟶LR eq tm)
  sameTm⟶LR (⟶compSucc eq) (tmSucc tm) = tmSucc (sameTm⟶LR eq tm)

  sameTm⟶LR (⟶compApp₁ red x) (tmApp tm tm₁) = tmApp (sameTm⟶LR red tm) tm₁
  sameTm⟶LR (⟶compApp₂ x red) (tmApp tm tm₁) = tmApp tm (sameTm⟶LR red tm₁)
  sameTm⟶LR (⟶compRec₁ red _ _) (tmRec tm tm₁ tm₂) =
    tmRec (sameTm⟶LR red tm) tm₁ tm₂
  sameTm⟶LR (⟶compRec₂ _ red _) (tmRec tm tm₁ tm₂) =
    tmRec tm (sameTm⟶LR red tm₁) tm₂
  sameTm⟶LR (⟶compRec₃ _ _ red) (tmRec tm tm₁ tm₂) =
    tmRec tm tm₁ (sameTm⟶LR red tm₂)

  sameTm⟶RL : ∀{Θ Γ Δ A t s}
              → Θ ∷ Δ ++ Γ ⊢ t ⟶ s ∶ A → Tm (clen Γ) s → Tm (clen Γ) t
  sameTm⟶RL (⟶β x x₁) tm = liftTm _ (tmApp (tmLam (tyClosed x)) (tyClosed x₁))
  sameTm⟶RL (⟶recZ x x₁) tm = liftTm _ (tmRec (tyClosed x) (tyClosed x₁) tmZero)
  sameTm⟶RL (⟶recS x x₁ x₂) (tmApp tm (tmRec tm₁ tm₂ tm₃)) =
    tmRec tm₁ tm₂ (tmSucc tm₃)
  sameTm⟶RL (⟶ξ eq) (tmLam tm) = tmLam (sameTm⟶RL eq tm)
  sameTm⟶RL (⟶compSucc eq) (tmSucc tm) = tmSucc (sameTm⟶RL eq tm)
  sameTm⟶RL (⟶compApp₁ red x) (tmApp tm tm₁) = tmApp (sameTm⟶RL red tm) tm₁
  sameTm⟶RL (⟶compApp₂ x red) (tmApp tm tm₁) = tmApp tm (sameTm⟶RL red tm₁)
  sameTm⟶RL (⟶compRec₁ red x x₁) (tmRec tm tm₁ tm₂) =
    tmRec (sameTm⟶RL red tm) tm₁ tm₂
  sameTm⟶RL (⟶compRec₂ x red x₁) (tmRec tm tm₁ tm₂) =
    tmRec tm (sameTm⟶RL red tm₁) tm₂
  sameTm⟶RL (⟶compRec₃ x x₁ red) (tmRec tm tm₁ tm₂) =
    tmRec tm tm₁ (sameTm⟶RL red tm₂)

  sameTm∼LR : ∀{Θ Γ Δ A t s}
            → Θ ∷ Δ ++ Γ ⊢ t ∼ s ∶ A → Tm (clen Γ) t → Tm (clen Γ) s
  sameTm∼LR (~⟶ x) tm = sameTm⟶LR x tm
  sameTm∼LR (∼refl x) tm = tm
  sameTm∼LR (∼symm eq) tm = sameTm∼RL eq tm
  sameTm∼LR (∼trans eq eq₁) tm = sameTm∼LR eq₁ (sameTm∼LR eq tm)

  sameTm∼RL : ∀{Θ Γ Δ A t s}
            → Θ ∷ Δ ++ Γ ⊢ t ∼ s ∶ A → Tm (clen Γ) s → Tm (clen Γ) t
  sameTm∼RL (~⟶ x) tm = sameTm⟶RL x tm
  sameTm∼RL (∼refl x) tm = tm
  sameTm∼RL (∼symm eq) tm = sameTm∼LR eq tm
  sameTm∼RL (∼trans eq eq₁) tm = sameTm∼RL eq (sameTm∼RL eq₁ tm)

≡to∼R : ∀{Θ Γ A t s s'} → s ≡ s' → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Γ ⊢ t ∼ s' ∶ A
≡to∼R refl eq = eq

≡to∼L : ∀{Θ Γ A t t' s} → t ≡ t' → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Γ ⊢ t' ∼ s ∶ A
≡to∼L refl eq = eq

≡∼ : ∀{Θ Θ' Γ Δ A A' t t' s s'}
   → Θ ∷ Γ ⊢ t ∼ s ∶ A
   → Θ ≡ Θ' → Γ ≡ Δ → A ≡ A' → t ≡ t' → s ≡ s'
   → Θ' ∷ Δ ⊢ t' ∼ s' ∶ A'
≡∼ eq refl refl refl refl refl = eq

≡⟶ : ∀{Θ Θ' Γ Δ A A' t t' s s'}
   → Θ ∷ Γ ⊢ t ⟶ s ∶ A
   → Θ ≡ Θ' → Γ ≡ Δ → A ≡ A' → t ≡ t' → s ≡ s'
   → Θ' ∷ Δ ⊢ t' ⟶ s' ∶ A'
≡⟶ eq refl refl refl refl refl = eq

--------------------------------------------------------------------------------
-- Meta weakening

wkₗ⟶ : ∀{Θ Γ A t s} Δ → Θ ∷ Γ ⊢ t ⟶ s ∶ A → Θ ++ Δ ∷ Γ ⊢ t ⟶ s ∶ A
wkₗ⟶ Δ (⟶β td sd) = ⟶β (wkMeta Δ td) (wkMeta Δ sd)
wkₗ⟶ Δ (⟶recZ zd sd) = ⟶recZ (wkMeta Δ zd) (wkMeta Δ sd)
wkₗ⟶ Δ (⟶recS zd sd nd) = ⟶recS (wkMeta Δ zd) (wkMeta Δ sd) (wkMeta Δ nd)
wkₗ⟶ Δ (⟶ξ red) = ⟶ξ (wkₗ⟶ Δ red)
wkₗ⟶ Δ (⟶compSucc red) = ⟶compSucc (wkₗ⟶ Δ red)
wkₗ⟶ Δ (⟶compApp₁ red x) = ⟶compApp₁ (wkₗ⟶ Δ red) (wkMeta Δ x)
wkₗ⟶ Δ (⟶compApp₂ x red) = ⟶compApp₂ (wkMeta Δ x) (wkₗ⟶ Δ red)
wkₗ⟶ Δ (⟶compRec₁ red x x₁) = ⟶compRec₁ (wkₗ⟶ Δ red) (wkMeta Δ x) (wkMeta Δ x₁)
wkₗ⟶ Δ (⟶compRec₂ x red x₁) = ⟶compRec₂ (wkMeta Δ x) (wkₗ⟶ Δ red) (wkMeta Δ x₁)
wkₗ⟶ Δ (⟶compRec₃ x x₁ red) = ⟶compRec₃ (wkMeta Δ x) (wkMeta Δ x₁) (wkₗ⟶ Δ red)

wkₗ∼ : ∀{Θ Γ A t s} Δ → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ++ Δ ∷ Γ ⊢ t ∼ s ∶ A
wkₗ∼ Δ (~⟶ x) = ~⟶ (wkₗ⟶ Δ x)
wkₗ∼ Δ (∼refl x) = ∼refl (wkMeta Δ x)
wkₗ∼ Δ (∼symm eq) = ∼symm (wkₗ∼ Δ eq)
wkₗ∼ Δ (∼trans eq eq₁) = ∼trans (wkₗ∼ Δ eq) (wkₗ∼ Δ eq₁)

--------------------------------------------------------------------------------
-- Weakening

⟶wk : ∀{Θ Γ Δ A t s w} → Δ ⊢ᵣ w ∶ Γ
      → Θ ∷ Γ ⊢ t ⟶ s ∶ A → Θ ∷ Δ ⊢ wk t w ⟶ wk s w ∶ A
⟶wk w (⟶β td sd) = ≡⟶ (⟶β td sd) refl refl refl
  (sym (null-wk (tmApp (tmLam (tyClosed td)) (tyClosed sd))))
  (sym (null-wk (sub-cover-lemma 0 0 (tyClosed td) (tyClosed sd))))
⟶wk w (⟶recZ zd sd) = ≡⟶ (⟶recZ zd sd) refl refl refl
  (sym (null-wk (tmRec (tyClosed zd) (tyClosed sd) tmZero)))
  (sym (null-wk (tyClosed zd)))
⟶wk w (⟶recS zd sd nd) = ≡⟶ (⟶recS zd sd nd) refl refl refl
  (sym (null-wk (tmRec tmz tms (tmSucc tmn))))
  (sym (null-wk (tmApp (tmApp tms tmn) (tmRec tmz tms tmn))))
  where tmz = tyClosed zd ; tms = tyClosed sd ; tmn = tyClosed nd
⟶wk w (⟶ξ red) = ⟶ξ (⟶wk (⊢Skip w) red)
⟶wk w (⟶compSucc red) = ⟶compSucc (⟶wk w red)
⟶wk w (⟶compApp₁ red x) = ⟶compApp₁ (⟶wk w red) (⊢wk x w)
⟶wk w (⟶compApp₂ x red) = ⟶compApp₂ (⊢wk x w) (⟶wk w red)
⟶wk w (⟶compRec₁ red x x₁) = ⟶compRec₁ (⟶wk w red) (⊢wk x w) (⊢wk x₁ w)
⟶wk w (⟶compRec₂ x red x₁) = ⟶compRec₂ (⊢wk x w) (⟶wk w red) (⊢wk x₁ w)
⟶wk w (⟶compRec₃ x x₁ red) = ⟶compRec₃ (⊢wk x w) (⊢wk x₁ w) (⟶wk w red)

∼wk : ∀{Θ Γ Δ A t s w} → Δ ⊢ᵣ w ∶ Γ
    → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Δ ⊢ wk t w ∼ wk s w ∶ A
∼wk w (~⟶ x) = ~⟶ (⟶wk w x)
∼wk w (∼refl x) = ∼refl (⊢wk x w)
∼wk w (∼symm eq) = ∼symm (∼wk w eq)
∼wk w (∼trans eq eq₁) = ∼trans (∼wk w eq) (∼wk w eq₁)

wk⟶ : ∀{Θ Γ Δ A t s} → Θ ∷ Γ ⊢ t ⟶ s ∶ A → Θ ∷ Δ ++ Γ ⊢ t ⟶ s ∶ A
wk⟶ (⟶β x x₁) = ⟶β x x₁
wk⟶ (⟶recZ x x₁) = ⟶recZ x x₁
wk⟶ (⟶recS x x₁ x₂) = ⟶recS x x₁ x₂
wk⟶ (⟶ξ eq) = ⟶ξ (wk⟶ eq)
wk⟶ (⟶compSucc eq) = ⟶compSucc (wk⟶ eq)
wk⟶ (⟶compApp₁ red x) = ⟶compApp₁ (wk⟶ red) (wkTerm x)
wk⟶ (⟶compApp₂ x red) = ⟶compApp₂ (wkTerm x) (wk⟶ red)
wk⟶ (⟶compRec₁ red x x₁) = ⟶compRec₁ (wk⟶ red) (wkTerm x) (wkTerm x₁)
wk⟶ (⟶compRec₂ x red x₁) = ⟶compRec₂ (wkTerm x) (wk⟶ red) (wkTerm x₁)
wk⟶ (⟶compRec₃ x x₁ red) = ⟶compRec₃ (wkTerm x) (wkTerm x₁) (wk⟶ red)

wk∼ : ∀{Θ Γ Δ A t s} → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Δ ++ Γ ⊢ t ∼ s ∶ A
wk∼ (~⟶ x) = ~⟶ (wk⟶ x)
wk∼ (∼refl x) = ∼refl (wkTerm x)
wk∼ (∼symm eq) = ∼symm (wk∼ eq)
wk∼ (∼trans eq eq₁) = ∼trans (wk∼ eq) (wk∼ eq₁)

--------------------------------------------------------------------------------
-- Derived equalities

-- Computation rules
~β : ∀{Θ Γ A B t s}
   → Θ ∷ ◇ # A ⊢ t ∶ B → Θ ∷ ◇ ⊢ s ∶ A
   → Θ ∷ Γ ⊢ (Lam t · s) ∼ sub t (Id , s) ∶ B
~β td sd = ~⟶ (⟶β td sd)

~recZ : ∀{Θ Γ A z s}
      → Θ ∷ ◇ ⊢ z ∶ A → Θ ∷ ◇ ⊢ s ∶ N => A => A
      → Θ ∷ Γ ⊢ Rec z s Zero ∼ z ∶ A
~recZ zd sd = ~⟶ (⟶recZ zd sd)

~recS : ∀{Θ Γ A z s n}
      → Θ ∷ ◇ ⊢ z ∶ A → Θ ∷ ◇ ⊢ s ∶ N => A => A → Θ ∷ ◇ ⊢ n ∶ N
      → Θ ∷ Γ ⊢ Rec z s (Succ n) ∼ s · n · Rec z s n ∶ A
~recS zd sd nd = ~⟶ (⟶recS zd sd nd)

-- Compatibility rules
∼ξ : ∀{Θ Γ A B t t'} → Θ ∷ Γ # A ⊢ t ∼ t' ∶ B → Θ ∷ Γ ⊢ Lam t ∼ Lam t' ∶ A => B
∼ξ (~⟶ x) = ~⟶ (⟶ξ x)
∼ξ (∼refl x) = ∼refl (lam x)
∼ξ (∼symm eq) = ∼symm (∼ξ eq)
∼ξ (∼trans eq eq₁) = ∼trans (∼ξ eq) (∼ξ eq₁)

∼compSucc : ∀{Θ Γ t t'} → Θ ∷ Γ ⊢ t ∼ t' ∶ N → Θ ∷ Γ ⊢ Succ t ∼ Succ t' ∶ N
∼compSucc (~⟶ x) = ~⟶ (⟶compSucc x)
∼compSucc (∼refl x) = ∼refl (sS x)
∼compSucc (∼symm x) = ∼symm (∼compSucc x)
∼compSucc (∼trans x x₁) = ∼trans (∼compSucc x) (∼compSucc x₁)

∼compApp₁  : ∀{Γ Γ' r r' s A B}
           → Γ ∷ Γ' ⊢ r ∼ r' ∶ A => B → Γ ∷ Γ' ⊢ s ∶ A
           → Γ ∷ Γ' ⊢ r · s ∼ r' · s ∶ B
∼compApp₁ (~⟶ x₁) x = ~⟶ (⟶compApp₁ x₁ x)
∼compApp₁ (∼refl x₁) x = ∼refl (x₁ ● x)
∼compApp₁ (∼symm eq) x = ∼symm (∼compApp₁ eq x)
∼compApp₁ (∼trans eq eq₁) x = ∼trans (∼compApp₁ eq x) (∼compApp₁ eq₁ x)

∼compApp₂  : ∀{Γ Γ' r s s' A B}
           → Γ ∷ Γ' ⊢ r ∶ A => B → Γ ∷ Γ' ⊢ s ∼ s' ∶ A
           → Γ ∷ Γ' ⊢ r · s ∼ r · s' ∶ B
∼compApp₂ x (~⟶ x₁) = ~⟶ (⟶compApp₂ x x₁)
∼compApp₂ x (∼refl x₁) = ∼refl (x ● x₁)
∼compApp₂ x (∼symm eq) = ∼symm (∼compApp₂ x eq)
∼compApp₂ x (∼trans eq eq₁) = ∼trans (∼compApp₂ x eq) (∼compApp₂ x eq₁)

∼compApp : ∀{Γ Γ' r r' s s' A B}
         → Γ ∷ Γ' ⊢ r ∼ r' ∶ A => B → Γ ∷ Γ' ⊢ s ∼ s' ∶ A
         → Γ ∷ Γ' ⊢ r · s ∼ r' · s' ∶ B
∼compApp eq eq' =
  ∼trans (∼compApp₁ eq (proj₁ (∼lemma eq'))) (∼compApp₂ (proj₂ (∼lemma eq)) eq')

∼compRec₁  : ∀{Θ Γ A z s n z'}
               → Θ ∷ Γ ⊢ z ∼ z' ∶ A
               → Θ ∷ Γ ⊢ s ∶ N => A => A
               → Θ ∷ Γ ⊢ n ∶ N
               → Θ ∷ Γ ⊢ Rec z s n ∼ Rec z' s n ∶ A
∼compRec₁ (~⟶ x) sd nd = ~⟶ (⟶compRec₁ x sd nd)
∼compRec₁ (∼refl x) sd nd = ∼refl (rec x sd nd)
∼compRec₁ (∼symm eq) sd nd = ∼symm (∼compRec₁ eq sd nd)
∼compRec₁ (∼trans eq eq₁) sd nd = ∼trans (∼compRec₁ eq sd nd) (∼compRec₁ eq₁ sd nd)

∼compRec₂  : ∀{Θ Γ A z s n s'}
               → Θ ∷ Γ ⊢ z ∶ A
               → Θ ∷ Γ ⊢ s ∼ s' ∶ N => A => A
               → Θ ∷ Γ ⊢ n ∶ N
               → Θ ∷ Γ ⊢ Rec z s n ∼ Rec z s' n ∶ A
∼compRec₂ zd (~⟶ x) nd = ~⟶ (⟶compRec₂ zd x nd)
∼compRec₂ zd (∼refl x) nd = ∼refl (rec zd x nd)
∼compRec₂ zd (∼symm eq) nd = ∼symm (∼compRec₂ zd eq nd)
∼compRec₂ zd (∼trans eq eq₁) nd = ∼trans (∼compRec₂ zd eq nd) (∼compRec₂ zd eq₁ nd)

∼compRec₃  : ∀{Θ Γ A z s n n'}
               → Θ ∷ Γ ⊢ z ∶ A
               → Θ ∷ Γ ⊢ s ∶ N => A => A
               → Θ ∷ Γ ⊢ n ∼ n' ∶ N
               → Θ ∷ Γ ⊢ Rec z s n ∼ Rec z s n' ∶ A
∼compRec₃ zd sd (~⟶ x) = ~⟶ (⟶compRec₃ zd sd x)
∼compRec₃ zd sd (∼refl x) = ∼refl (rec zd sd x)
∼compRec₃ zd sd (∼symm eq) = ∼symm (∼compRec₃ zd sd eq)
∼compRec₃ zd sd (∼trans eq eq₁) = ∼trans (∼compRec₃ zd sd eq) (∼compRec₃ zd sd eq₁)

∼compRec : ∀{Θ Γ A z z' s s' n n'}
         → Θ ∷ Γ ⊢ z ∼ z' ∶ A
         → Θ ∷ Γ ⊢ s ∼ s' ∶ N => A => A
         → Θ ∷ Γ ⊢ n ∼ n' ∶ N
         → Θ ∷ Γ ⊢ Rec z s n ∼ Rec z' s' n' ∶ A
∼compRec eq eq' eq'' =
   ∼trans (∼compRec₁ eq (proj₁ (∼lemma eq')) (proj₁ (∼lemma eq'')))
  (∼trans (∼compRec₂ (proj₂ (∼lemma eq)) eq' (proj₁ (∼lemma eq'')))
          (∼compRec₃ (proj₂ (∼lemma eq)) (proj₂ (∼lemma eq')) eq''))


⊢lsub : ∀{Θ Γ A B t a b}
      → Θ # A ∷ Γ ⊢ t ∶ B → Θ ∷ ◇ ⊢ a ∼ b ∶ A
      → Θ ∷ Γ ⊢ t ⟨ clen Θ ↦ a ⟩ ∼ t ⟨ clen Θ ↦ b ⟩ ∶ B
⊢lsub {Θ} (free {n = n} x) eq with n ≟ clen Θ
⊢lsub (free x) eq | yes p rewrite p | l-maps-here x = wk∼ eq
⊢lsub {Θ} (free {n = .(clen Θ)} here) eq | no ¬p = ⊥-elim (¬p refl)
⊢lsub {Θ} (free {n = n} (there x)) eq | no ¬p = ∼refl (free x)
⊢lsub (var x) eq = ∼refl (var x)
⊢lsub (lam td) eq = ∼ξ (⊢lsub td eq)
⊢lsub (td ● sd) eq = ∼compApp (⊢lsub td eq) (⊢lsub sd eq)
⊢lsub zZ eq = ∼refl zZ
⊢lsub (sS td) eq = ∼compSucc (⊢lsub td eq)
⊢lsub (rec td td₁ td₂) eq = 
  ∼compRec (⊢lsub td eq) (⊢lsub td₁ eq) (⊢lsub td₂ eq)
