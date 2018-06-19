module Semantics.Completeness.Type.Lemmata where

open import Syntax hiding (tmSuccLemma)
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_)
open import Semantics.Domain.Domain
open import Semantics.Completeness.Type.SemTy
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Empty

open SemTy
open _∈_
open ⟦_⟧≃⟦_⟧_∈tm_
open _●_∈ap_
open rec_·_·_∈r_

≡ap : ∀{f g a A} → f ≡ g → f ● a ∈ap A → g ● a ∈ap A
≡ap refl x = x

appLemma : ∀{A B} {f a : D} → f ∈ A ==> B → a ∈ A → f ● a ∈ap B
appLemma {A} {f = f} (in∈ (_ ,, h)) (in∈ a) = ≡ap (id-wk 0 f) (h {w = Id} a)

opInNat : ∀{n} → n ∈ Nat → N-Redex-Op n
opInNat (in∈ natZ) = nroZ
opInNat (in∈ (natS p)) = nroS (isNf Nat p)
opInNat (in∈ (natNe x)) = nroNe x

recLemma : ∀{A z s t} → z ∈ A → s ∈ (Nat ==> A ==> A) → t ∈ Nat
         → rec z · s · t ∈r A
recLemma {A} zp sp tp
  with decN-Redex (isNf A (wit zp))
                  (isNf (Nat ==> A ==> A) (wit sp))
                  (opInNat tp)
recLemma {A} zp sp (in∈ natZ) | inj₁ x = record { ∈tm = zp ; ↘rec = rZ x }
recLemma {A} zp sp (in∈ (natS p)) | inj₁ x =
  record { ∈tm = ∈tm ap' ; ↘rec = rS x (↘rec rk) (↘ap ap) (↘ap ap') }
  where
    rk = recLemma {A} zp sp (in∈ p) ; ap = appLemma {Nat} {A ==> A} sp (in∈ p)
    ap' = appLemma {A} {A} (∈tm ap) (∈tm rk)

recLemma {A} zp sp (in∈ (natNe ())) | inj₁ (NrdxZ x x₁)
recLemma {A} zp sp (in∈ (natNe ())) | inj₁ (NrdxS x x₁ x₂)
recLemma {A} zp sp tp | inj₂ y = record { ∈tm = in∈ (hasNe A y) ; ↘rec = rNe y }

tmAppLemma : ∀{A B t t' s s' ρ}
           → ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm ⟦ A => B ⟧ₜ
           → ⟦ s ⟧≃⟦ s' ⟧ ρ ∈tm ⟦ A ⟧ₜ
           → ⟦ t · s ⟧≃⟦ t' · s' ⟧ ρ ∈tm ⟦ B ⟧ₜ
tmAppLemma t s =
  ⟨ ∈tm ap ∣ eApp (↘tm1 t) (↘tm1 s) (↘ap ap) ∣ eApp (↘tm2 t) (↘tm2 s) (↘ap ap) ⟩
  where ap = appLemma (∈tm t) (∈tm s)

tmSuccLemma : ∀{t t' ρ}
            → ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm Nat
            → ⟦ Succ t ⟧≃⟦ Succ t' ⟧ ρ ∈tm Nat
tmSuccLemma ⟨ in∈ x ∣ e1 ∣ e2 ⟩ = ⟨ in∈ (natS x) ∣ eSucc e1 ∣ eSucc e2 ⟩

shLemma : ∀{A B ρ t t'}
         → (∀{a w} → a ∈ ⟦ A ⟧ₜ → ⟦ t ⟧≃⟦ t' ⟧ (ρ · w , a) ∈tm ⟦ B ⟧ₜ)
         → ⟦ t ⟧≃⟦ t' ⟧ sh ρ ∈tm ⟦ B ⟧ₜ
shLemma h = h hasBound

tmLamLemma : ∀{A B ρ t t'}
           → (∀{a w} → a ∈ ⟦ A ⟧ₜ → ⟦ t ⟧≃⟦ t' ⟧ (ρ · w , a) ∈tm ⟦ B ⟧ₜ)
           → ⟦ Lam t ⟧≃⟦ Lam t' ⟧ ρ ∈tm ⟦ A => B ⟧ₜ
tmLamLemma {A} {B} {ρ} {t} {t'} ht' =
  ⟨ in∈ (nfl ,, goal) ∣ eLam (↘tm1 ht) ∣ eLam (↘tm2 ht) ⟩
  where
    ht = shLemma {A} {B} ht'
    nfl = nfLam (nfEval (↘tm1 ht))
    goal : ∀{a w} → P ⟦ A ⟧ₜ a → Lam (wk (d ht) (Skip w)) ● a ∈ap ⟦ B ⟧ₜ
    goal pa with decβ-Redex (nfWkLemma nfl) (isNf ⟦ A ⟧ₜ pa)
    goal {a} {w} pa | inj₁ x = 
      record { ∈tm = ∈tm aux ; ↘ap = ●β x (sub-comm {t} e1 e2) }
      where
        aux = ht' (in∈ pa)
        e1 = ≡Eval (trans (wk-subst t) (eq-sub sh-skip t)) refl (wkEval (↘tm1 ht))
        e2 = ≡Eval (eq-sub (consˢ (symmˢ sub-id-L)) t) refl (↘tm1 aux)
    goal pa | inj₂ y = record { ∈tm = in∈ (hasNe ⟦ B ⟧ₜ y) ; ↘ap = ●Ne y }

tmRecLemma : ∀{A z s t z' s' t' ρ}
           → ⟦ z ⟧≃⟦ z' ⟧ ρ ∈tm ⟦ A ⟧ₜ
           → ⟦ s ⟧≃⟦ s' ⟧ ρ ∈tm ⟦ N => A => A ⟧ₜ
           → ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm Nat
           → ⟦ Rec z s t ⟧≃⟦ Rec z' s' t' ⟧ ρ ∈tm ⟦ A ⟧ₜ
tmRecLemma zh sh th =
  ⟨ ∈tm rk ∣ eRec (↘tm1 zh) (↘tm1 sh) (↘tm1 th) (↘rec rk)
           ∣ eRec (↘tm2 zh) (↘tm2 sh) (↘tm2 th) (↘rec rk) ⟩
  where rk = recLemma (∈tm zh) (∈tm sh) (∈tm th)

Eval0 : ∀{n t d ρ} → Tm n t → Eval sub t (shift n ρ) ↘ d → Tm n d
Eval0 {n} tm e = Eval-Tm (subst (Tm n) (sym (null-sub tm)) tm) e

tmRecZLemma : ∀{A z s ρ}
    → ⟦ z ⟧≃⟦ z ⟧ ρ ∈tm ⟦ A ⟧ₜ
    → ⟦ s ⟧≃⟦ s ⟧ ρ ∈tm ⟦ N => A => A ⟧ₜ
    → Tm 0 z → Tm 0 s
    → ⟦ Rec z s Zero ⟧≃⟦ z ⟧ ρ ∈tm ⟦ A ⟧ₜ
tmRecZLemma zp sp tmz tms =
  ⟨ ∈tm zp
  ∣ eRec (↘tm1 zp) (↘tm1 sp) eZero (rZ (NrdxZ
     (Eval0 tmz (↘tm1 zp)) (Eval0 tms (↘tm1 sp))))
  ∣ ↘tm1 zp ⟩

tmRecSLemma : ∀{A z s n ρ}
    → ⟦ z ⟧≃⟦ z ⟧ ρ ∈tm ⟦ A ⟧ₜ
    → ⟦ s ⟧≃⟦ s ⟧ ρ ∈tm ⟦ N => A => A ⟧ₜ
    → ⟦ n ⟧≃⟦ n ⟧ ρ ∈tm Nat
    → Tm 0 z → Tm 0 s → Tm 0 n
    → ⟦ Rec z s (Succ n) ⟧≃⟦ s · n · Rec z s n ⟧ ρ ∈tm ⟦ A ⟧ₜ
tmRecSLemma {A = A} zp sp np tmz tms tmn
  with tmRecLemma {A} zp sp np
     | tmAppLemma {A} {A} (tmAppLemma {N} {A => A} sp np) (tmRecLemma {A} zp sp np)
tmRecSLemma {A} zp sp np tmz tms tmn
  | ⟨ tm ∣ eRec e1 e3 e4 x ∣ e2 ⟩
  | ⟨ tm' ∣ eApp (eApp e1' e5 x₂) (eRec e1'' e6 e7 x₃) x₁ ∣ e2' ⟩ =
    ⟨ tm' ∣ eRec e1 e3 (eSucc e4)
      (rS (NrdxS (Eval0 tmz e1) (Eval0 tms e3) (Eval0 tmn e4))
          x (≡App (Eval-fun e1' e3) (Eval-fun e5 e4) refl x₂)
            (≡App refl (rec-fun x₃ (≡Rec (Eval-fun e1 e1'') (Eval-fun e3 e6)
              (Eval-fun e4 e7) refl x)) refl x₁)) ∣ e2' ⟩

tmSubLemma : ∀{t ρ t' s s' d}
           → t [ sh ρ ]↘ t' → s [ ρ ]↘ s' → t' [ Id , s' ]↘ d
           → sub t (Id , s) [ ρ ]↘ d
tmSubLemma {t} {ρ} {t'} {s} {s'} {d} e1 e3 sb =
  ≡Eval (trans (sub-comp t) (sym (trans (sub-comp t)
    (eq-sub (transˢ (sub-comp-R {s} Id ρ) (consˢ (transˢ (id-comp-L ρ)
      (symmˢ sub-id-L)))) t)))) refl uhm
  where
    uhm : Eval sub (sub t (sh ρ)) (Id , sub s ρ) ↘ d
    uhm = sub-comm2 {sub t (sh ρ)} 0 (sub-unswap e1 sb) e3

tmβLemma : ∀{A B t s ρ}
         → ⟦ Lam t ⟧≃⟦ Lam t ⟧ ρ ∈tm ⟦ A => B ⟧ₜ
         → ⟦ s ⟧≃⟦ s ⟧ ρ ∈tm ⟦ A ⟧ₜ
         → Tm 1 t → Tm 0 s
         → ⟦ Lam t · s ⟧≃⟦ sub t (Id , s) ⟧ ρ ∈tm ⟦ B ⟧ₜ
tmβLemma {A} {B} l s tmt tms with tmAppLemma {A = A} {B = B} l s
tmβLemma {t = t} l sp tmt tms 
  | ⟨ x ∣ ap@(eApp (eLam e1) e3 (●β _ sb)) ∣ _ ⟩ = 
    ⟨ x ∣ ap ∣ tmSubLemma {t} e1 e3 sb ⟩
tmβLemma _ _ tmt tms | ⟨ x ∣ eApp (eLam e1) e3 (●Ne ne) ∣ _ ⟩ = 
  ⊥-elim (neBeta ne (Eval0 tmt e1) (Eval0 tms e3))
