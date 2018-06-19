module Syntax.Evaluation.SubSwap where

open import Utils
open import Data.Nat
open import Data.Sum
open import Syntax.Evaluation.Evaluation
open import Syntax.Raw
open import Syntax.Evaluation.NormalForm
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)
open import Syntax.Evaluation.Properties
open import Syntax.Evaluation.NeTransfer

record SubComp (t b : Term) (σ : Subst) : Set where
  field
    {tm} : Term
    ev1 : Eval t ↘ tm
    ev2 : Eval sub tm σ ↘ b
open SubComp

●-sub-swap : ∀{t t' s s' b σ}
            → SubComp t t' σ → SubComp s s' σ → t' ● s' ↘ b
            → SubComp (t · s) b σ
●-sub-swap {t} {_} {s} {_} {b} {σ} ih ih' ap@(●β rdx ev) = goal
  where
    rdx? = decβ-Redex' (nfEval (ev1 ih)) (nfEval (ev1 ih'))
      (NeLamLemma (nfEval (ev1 ih)) (ev2 ih))
    goal : SubComp (t · s) b σ
    goal with rdx?
    goal | inj₁ (q ,, tee ,, p) =
      record { ev1 = eApp (ev1 ih) (ev1 ih') (≡App (sym p)
                          refl refl (●β brdx evl)) ; ev2 = evlb }
      where
        e1 = ≡Eval (null-sub (β-Redex-Tm-t q)) refl (ev2 ih)
        e2 = ≡Eval (null-sub (β-Redex-Tm-s q)) refl (ev2 ih')
        lam-eq = trans (sym p) (Eval-fun (nfSelf (nfEval (ev1 ih))) e1)
        ss-eq = Eval-fun (nfSelf (nfEval (ev1 ih'))) e2
        brdx : β-Redex (Lam tee) (tm ih')
        brdx rewrite lam-eq | ss-eq = rdx
        evl : Eval sub tee (Id , tm ih') ↘ _
        evl = ≡Eval (cong₂ sub (sym (Lam-inj lam-eq))
          (cong₂ _,_ refl (sym ss-eq))) refl ev
        evlb : Eval sub b σ ↘ b
        evlb = ≡Eval (sym (null-sub (Eval-Tm (sub-cover-lemma 0 0
          (β-Redex-Tm-Lam-t rdx) (β-Redex-Tm-s rdx)) ev)))
            refl (nfSelf (nfEval ev))
    goal | inj₂ y =
      record { ev1 = eApp (ev1 ih) (ev1 ih') (●Ne y)
             ; ev2 = eApp (ev2 ih) (ev2 ih') ap }
●-sub-swap {t} {_} {s} ih ih' (●Ne x) =
  record { ev1 = eApp (ev1 ih) (ev1 ih')
                   (●Ne (NeAppTransferLemma (ev2 ih) (ev2 ih') (ev1 ih) (ev1 ih') x))
         ; ev2 = eApp (ev2 ih) (ev2 ih') (●Ne x) }

rec-sub-swap : ∀{z z' s s' t t' b σ}
              → SubComp z z' σ
              → SubComp s s' σ
              → SubComp t t' σ
              → Rec z' · s' · t' ↘ b
              → SubComp (Rec z s t) b σ
rec-sub-swap {z} {s = s} {t = t} {σ} ihz ihs iht r@(rZ x) = goal
  where
    rdx? = decN-Redex-Z (nfEval (ev1 ihz)) (nfEval (ev1 ihs))
             (nfEval (ev1 iht)) (NeZeroLemma (nfEval (ev1 iht)) (ev2 iht))
    goal : SubComp (Rec z s t) _ _
    goal with rdx?
    goal | inj₁ (q ,, x) =
      record { ev1 = eRec (ev1 ihz) (ev1 ihs) (ev1 iht)
                          (≡Rec refl refl (sym x) refl (rZ rdxx))
             ; ev2 = ≡Eval (sym (trans (null-sub (N-Redex-Tm-z q)) eqq))
                       refl (nfSelf (nfEval (ev2 ihz))) }
      where
        rdxx = NrdxZ (N-Redex-Tm-z q) (N-Redex-Tm-s q)
        eqq = Eval-fun (nfSelf (nfEval (ev1 ihz)))
                (≡Eval (null-sub (N-Redex-Tm-z q)) refl (ev2 ihz))
    goal | inj₂ y =
      record { ev1 = eRec (ev1 ihz) (ev1 ihs) (ev1 iht) (rNe y)
             ; ev2 = eRec (ev2 ihz) (ev2 ihs) (ev2 iht) r }

rec-sub-swap {z} {s = s} {t = t} {b = b} {σ} ihz ihs iht r@(rS x rk x₂ x₃) = goal
  where
    rdx? = decN-Redex-S (nfEval (ev1 ihz)) (nfEval (ev1 ihs)) (nfEval (ev1 iht))
                        (NeSuccLemma (nfEval (ev1 iht)) (ev2 iht))
    goal : SubComp (Rec z s t) b σ
    goal with rdx?
    goal | inj₁ (q ,, (tee ,, x)) =
      record { ev1 = eRec (ev1 ihz) (ev1 ihs) (ev1 iht)
                          (≡Rec refl refl (sym x) refl rekk)
             ; ev2 = ssbb }
      where
        e2 = ≡Eval (null-sub (N-Redex-Tm-z q)) refl (ev2 ihz)
        e3 = ≡Eval (null-sub (N-Redex-Tm-s q)) refl (ev2 ihs)
        e4 = ≡Eval (null-sub (N-Redex-Tm-t q)) refl (ev2 iht)
        eq2 = Eval-fun (nfSelf (nfEval (ev1 ihz))) e2
        eq3 = Eval-fun (nfSelf (nfEval (ev1 ihs))) e3
        eq4 = Eval-fun (nfSelf (nfEval (ev1 iht))) e4
        rdx : N-Redex (tm ihz) (tm ihs) (Succ tee)
        rdx = NrdxS (N-Redex-Tm-z q) (N-Redex-Tm-s q)
                    (tmSuccLemma (Tm≡ x refl (N-Redex-Tm-t q)))
        rekk =
          rS rdx (≡Rec (sym eq2) (sym eq3)
                 (Succ-inj (trans (sym eq4) x)) refl rk)
                 (≡App (sym eq3) (Succ-inj (trans (sym eq4) x)) refl x₂) x₃
        b0 = rec-Tm (Tm≡ eq2 refl (N-Redex-Tm-z q))
                    (Tm≡ eq3 refl (N-Redex-Tm-s q))
                    (Tm≡ eq4 refl (N-Redex-Tm-t q)) r
        ssbb = ≡Eval (sym (null-sub b0)) refl
            (nfSelf (nfRec (nfEval (ev2 ihz)) (nfEval (ev2 ihs)) (nfEval (ev2 iht)) r))
    goal | inj₂ y =
      record { ev1 = eRec (ev1 ihz) (ev1 ihs) (ev1 iht) (rNe y)
             ; ev2 = eRec (ev2 ihz) (ev2 ihs) (ev2 iht) r }
rec-sub-swap {z} {s = s} {t = t} {b = .(Rec _ _ _)} {σ} ihz ihs iht (rNe x) =
  record { ev1 =
    eRec (ev1 ihz) (ev1 ihs) (ev1 iht)
      (rNe (NeRecTransferLemma (ev2 ihz) (ev2 ihs) (ev2 iht) 
                                (ev1 ihz) (ev1 ihs) (ev1 iht) x)) 
         ; ev2 = eRec (ev2 ihz) (ev2 ihs) (ev2 iht) (rNe x) }

sub-swap : ∀{t σ b} → Eval sub t σ ↘ b → SubComp t b σ
sub-swap {Free x} eFree = record { ev1 = eFree ; ev2 = eFree }
sub-swap {Bound x} e = record { ev1 = eBound ; ev2 = e }
sub-swap {Lam t} (eLam e) = record { ev1 = eLam (ev1 ih) ; ev2 = eLam (ev2 ih) }
  where ih = sub-swap {t} e
sub-swap {t · s} (eApp e e₁ x) = ●-sub-swap (sub-swap {t} e) (sub-swap {s} e₁) x
sub-swap {Zero} eZero = record { ev1 = eZero ; ev2 = eZero }
sub-swap {Succ t} (eSucc e) = record { ev1 = eSucc (ev1 ih) ; ev2 = eSucc (ev2 ih) }
  where ih = sub-swap {t} e
sub-swap {Rec z s t} (eRec {r = r} e e₁ e₂ x) = 
  rec-sub-swap (sub-swap {z} e) (sub-swap {s} e₁) (sub-swap {t} e₂) x

sub-swap' : ∀{t a b σ} → Eval t ↘ a → Eval sub t σ ↘ b → Eval sub a σ ↘ b
sub-swap' {t} e1 e2 with sub-swap {t} e2
sub-swap' e1 e2 | record { tm = tm ; ev1 = ev1 ; ev2 = ev2 } =
  ≡Eval (cong₂ sub (Eval-fun ev1 e1) refl) refl ev2

sub-comm : ∀{t a b σ σ'}
         → Eval sub t σ ↘ b → Eval sub t (σ ·ˢ σ') ↘ a → Eval sub b σ' ↘ a
sub-comm {t} {σ = σ} {σ'} e1 e2
  rewrite sym (sub-comp {σ} {σ'} t) = sub-swap' e1 e2

●-sub-swap' : ∀{t t' s s' b σ}
             → Nf t → Nf s
             → Eval sub t σ ↘ t' → Eval sub s σ ↘ s' → t' ● s' ↘ b
             → Σ Term λ a → t ● s ↘ a × Eval sub a σ ↘ b
●-sub-swap' {t} {_} {s} nft ns et es ap 
  with ●-sub-swap {t = t} {s = s} (sub-swap et) (sub-swap es) ap
●-sub-swap' nft nfs et es ap | record { tm = tm ; ev1 = eApp ev3 ev4 x ; ev2 = ev2 } 
  rewrite Eval-fun (nfSelf nft) ev3 | Eval-fun (nfSelf nfs) ev4 = _ ,, x ,, ev2

rec-sub-swap' : ∀{z z' s s' t t' b σ}
              → Nf z → Nf s → Nf t
              → Eval sub z σ ↘ z' → Eval sub s σ ↘ s' → Eval sub t σ ↘ t'
              → Rec z' · s' · t' ↘ b
              → Σ Term λ a → Rec z · s · t ↘ a × Eval sub a σ ↘ b
rec-sub-swap' {z} {_} {s} {_} {t} nfz nfs nft ez es et r
  with rec-sub-swap {z = z} {s = s} {t = t} (sub-swap ez) (sub-swap es) (sub-swap et) r
rec-sub-swap' nfz nfs nft ez es et r |
  record { tm = tm ; ev1 = eRec ev3 ev4 ev5 x ; ev2 = ev2 }
  rewrite Eval-fun (nfSelf nfz) ev3
        | Eval-fun (nfSelf nfs) ev4
        | Eval-fun (nfSelf nft) ev5 = _ ,, (x ,, ev2)

Rec-Tm' : ∀{z z' s s' t t'}
        → Eval z ↘ z' → Eval s ↘ s' → Eval t ↘ t'
        → N-Redex z' s' t' → Tm 0 (Rec z s t)
Rec-Tm' ez es et rdx =
  tmRec (Eval-Tm' ez (N-Redex-Tm-z rdx))
        (Eval-Tm' es (N-Redex-Tm-s rdx))
        (Eval-Tm' et (N-Redex-Tm-t rdx))

sub-unswap : ∀{t a b σ} → Eval t ↘ a → Eval sub a σ ↘ b → Eval sub t σ ↘ b
sub-unswap eBound e2 = e2
sub-unswap eFree e2 = e2
sub-unswap eZero e2 = e2
sub-unswap (eSucc e1) (eSucc e2) = eSucc (sub-unswap e1 e2)
sub-unswap (eLam e1) (eLam e2) = eLam (sub-unswap e1 e2)
sub-unswap e@(eApp e1 e3 ap@(●β (βrdx x x₂) x₁)) e2 =
  ≡Eval (sym (null-sub (tmApp (Eval-Tm' e1 (tmLam x)) (Eval-Tm' e3 x₂))))
    (Eval-fun (≡Eval (sym (null-sub (Eval-Tm
      (sub-cover-lemma 0 0 x x₂) x₁))) refl (nfSelf (nfEval x₁))) e2) e
sub-unswap (eApp e1 e3 (●Ne x)) (eApp e2 e4 x₁) =
  eApp (sub-unswap e1 e2) (sub-unswap e3 e4) x₁
sub-unswap e@(eRec e1 e3 e4 (rZ x)) e2 =
  ≡Eval (sym (null-sub tmm))
        (Eval-fun (≡Eval (sym (null-sub (Eval-Tm tmm e)))
          refl (nfSelf (nfEval e))) e2) e
  where tmm = Rec-Tm' e1 e3 e4 x
sub-unswap e@(eRec e1 e3 e4 (rS x x₁ x₂ x₃)) e2 =
  ≡Eval (sym (null-sub tmm))
    (Eval-fun (≡Eval (sym (null-sub (Eval-Tm tmm e)))
      refl (nfSelf (nfEval e))) e2) e
  where tmm = Rec-Tm' e1 e3 e4 x
sub-unswap (eRec e1 e3 e4 (rNe x)) (eRec e2 e5 e6 x₁) =
  eRec (sub-unswap e1 e2) (sub-unswap e3 e5) (sub-unswap e4 e6) x₁

sub-uncomm : ∀{t a b σ σ'}
           → Eval sub t σ ↘ a → Eval sub a σ' ↘ b → Eval sub t (σ ·ˢ σ') ↘ b
sub-uncomm {t} e1 e2 = ≡Eval (sub-comp t) refl (sub-unswap e1 e2)
