module Syntax.Evaluation.Properties where

open import Utils
open import Data.Nat
open import Data.Sum
open import Syntax.Evaluation.Evaluation
open import Syntax.Raw
open import Syntax.Evaluation.NormalForm
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)

mutual
  ●-fun : ∀{t s a b} → t ● s ↘ a → t ● s ↘ b → a ≡ b
  ●-fun (●β x e1) (●β y e2) = Eval-fun e1 e2
  ●-fun (●β x x₁) (●Ne y) = ⊥-elim (NeApp¬β y x)
  ●-fun (●Ne x) (●β y x₂) = ⊥-elim (NeApp¬β x y)
  ●-fun (●Ne x) (●Ne x₁) = refl

  rec-fun : ∀{z s t a b}
          → Rec z · s · t ↘ a → Rec z · s · t ↘ b → a ≡ b
  rec-fun (rZ x) (rZ x₁) = refl
  rec-fun (rZ x) (rNe x₁) = ⊥-elim (NeRec¬N x₁ x)
  rec-fun (rS _ r1 ap1 ap3) (rS _ r2 ap2 ap4)
    with rec-fun r1 r2 | ●-fun ap1 ap2
  rec-fun (rS _ r1 ap1 ap3) (rS _ r2 ap2 ap4) | refl | refl = ●-fun ap3 ap4
  rec-fun (rS x r1 x₁ x₂) (rNe x₃) = ⊥-elim (NeRec¬N x₃ x)
  rec-fun (rNe x) (rZ x₁) = ⊥-elim (NeRec¬N x x₁)
  rec-fun (rNe x) (rS x₁ r2 x₂ x₃) = ⊥-elim (NeRec¬N x x₁)
  rec-fun (rNe x) (rNe x₁) = refl

  Eval-fun : ∀{t a b} → Eval t ↘ a → Eval t ↘ b → a ≡ b
  Eval-fun eBound eBound = refl
  Eval-fun eFree eFree = refl
  Eval-fun eZero eZero = refl
  Eval-fun (eSucc e1) (eSucc e2) = cong Succ (Eval-fun e1 e2)
  Eval-fun (eLam e1) (eLam e2) = cong Lam (Eval-fun e1 e2)
  Eval-fun (eApp e1 e2 x) (eApp e3 e4 x₁)
    with Eval-fun e1 e3 | Eval-fun e2 e4
  Eval-fun (eApp e1 e2 x) (eApp e3 e4 y) | refl | refl = ●-fun x y
  Eval-fun (eRec e1 e2 e3 x) (eRec e4 e5 e6 x₁)
    with Eval-fun e1 e4 | Eval-fun e2 e5 | Eval-fun e3 e6
  Eval-fun (eRec e1 e2 e3 x) (eRec e4 e5 e6 y) | refl | refl | refl = rec-fun x y

Eval-fun' : ∀{t s a b} → Eval t ↘ a → Eval s ↘ b → t ≡ s → a ≡ b
Eval-fun' e1 e2 refl = Eval-fun e1 e2

mutual
  neSelf : ∀{t} → Ne t → Eval t ↘ t
  neSelf ne with neView ne
  neSelf ne | NVApp x y = eApp (nfSelf x) (nfSelf y) (●Ne ne)
  neSelf ne | NVRec x y z = eRec (nfSelf x) (nfSelf y) (nfSelf z) (rNe ne)
  neSelf ne | NVFree = eFree
  neSelf ne | NVBound = eBound

  nfSelf : ∀{t} → Nf t → Eval t ↘ t
  nfSelf (nfLam nf) = eLam (nfSelf nf)
  nfSelf nfZero = eZero
  nfSelf (nfSucc nf) = eSucc (nfSelf nf)
  nfSelf (nfNe x) = neSelf x

mutual
  nfApp : ∀{t s a} → Nf t → Nf s → t ● s ↘ a → Nf a
  nfApp nft nfs (●β x e) = nfEval e
  nfApp nft nfs (●Ne x) = nfNe x

  nfRec : ∀{z s t a} → Nf z → Nf s → Nf t → Rec z · s · t ↘ a → Nf a
  nfRec nfz nfs nft (rZ x) = nfz
  nfRec nfz nfs (nfSucc nft) (rS x r x₁ x₂) =
    nfApp (nfApp nfs nft x₁) (nfRec nfz nfs nft r) x₂
  nfRec nfz nfs (nfNe ()) (rS x r x₁ x₂)
  nfRec nfz nfs nft (rNe x) = nfNe x

  nfEval : ∀{t a} → Eval t ↘ a → Nf a
  nfEval eBound = nfNe neBound
  nfEval eFree = nfNe neFree
  nfEval eZero = nfZero
  nfEval (eSucc e) = nfSucc (nfEval e)
  nfEval (eLam e) = nfLam (nfEval e)
  nfEval (eApp e e₁ x) = nfApp (nfEval e) (nfEval e₁) x
  nfEval (eRec e e₁ e₂ x) = nfRec (nfEval e) (nfEval e₁) (nfEval e₂) x

mutual
  ●-Tm : ∀{t s a n} → Tm n t → Tm n s → t ● s ↘ a → Tm n a
  ●-Tm {n = n} tmt tms (●β (βrdx x x₂) x₁) =
    liftTm n (Eval-Tm (sub-cover-lemma 0 0 x x₂) x₁)
  ●-Tm tmt tms (●Ne x) = tmApp tmt tms

  rec-Tm : ∀{z s t a n} → Tm n z → Tm n s → Tm n t
         → Rec z · s · t ↘ a → Tm n a
  rec-Tm tmz tms tmt (rZ x) = tmz
  rec-Tm tmz tms (tmSucc tmt) (rS x r x₁ x₂) =
    ●-Tm (●-Tm tms tmt x₁) (rec-Tm tmz tms tmt r) x₂
  rec-Tm tmz tms tmt (rNe x) = tmRec tmz tms tmt

  Eval-Tm : ∀{t s n} → Tm n t → Eval t ↘ s → Tm n s
  Eval-Tm tmFree eFree = tmFree
  Eval-Tm (tmVar x₁) eBound = tmVar x₁
  Eval-Tm (tmLam tm) (eLam e) = tmLam (Eval-Tm tm e)
  Eval-Tm (tmApp tm tm₁) (eApp e e₁ x) = ●-Tm (Eval-Tm tm e) (Eval-Tm tm₁ e₁) x
  Eval-Tm tmZero eZero = tmZero
  Eval-Tm (tmSucc tm) (eSucc e) = tmSucc (Eval-Tm tm e)
  Eval-Tm (tmRec tm tm₁ tm₂) (eRec e e₁ e₂ x) =
    rec-Tm (Eval-Tm tm e) (Eval-Tm tm₁ e₁) (Eval-Tm tm₂ e₂) x

mutual

  ●-¬Tm : ∀{t s a n} → t ● s ↘ a → ¬Tm n (t · s) → ¬Tm n a
  ●-¬Tm (●β (βrdx x x₂) x₁) (¬tmApp₁ tm) =
    ⊥-elim (¬Tm-lemma tm (tmLam (liftTm _ x)))
  ●-¬Tm (●β (βrdx x x₃) x₁) (¬tmApp₂ x₂ tm) =
    ⊥-elim (¬Tm-lemma tm (liftTm _ x₃))
  ●-¬Tm (●Ne x) tm = tm

  rec-¬Tm : ∀{z s t n a} → Rec z · s · t ↘ a → ¬Tm n (Rec z s t) → ¬Tm n a
  rec-¬Tm (rZ (NrdxZ x x₁)) (¬tmRec₁ tm) = ⊥-elim (¬Tm-lemma tm (liftTm _ x))
  rec-¬Tm (rZ (NrdxZ x x₁)) (¬tmRec₂ x₂ tm) = ⊥-elim (¬Tm-lemma tm (liftTm _ x₁))
  rec-¬Tm (rZ (NrdxZ x x₁)) (¬tmRec₃ x₂ x₃ ())
  rec-¬Tm (rS (NrdxS x x₃ x₄) r x₁ x₂) (¬tmRec₁ tm) =
    ⊥-elim (¬Tm-lemma tm (liftTm _ x))
  rec-¬Tm (rS (NrdxS x x₃ x₄) r x₁ x₂) (¬tmRec₂ x₅ tm) =
    ⊥-elim (¬Tm-lemma tm (liftTm _ x₃))
  rec-¬Tm (rS (NrdxS x x₃ x₄) r x₁ x₂) (¬tmRec₃ x₅ x₆ (¬tmSucc tm)) =
    ⊥-elim (¬Tm-lemma tm (liftTm _ x₄))
  rec-¬Tm (rNe x) tm = tm

  Eval-¬Tm : ∀{t a n} → Eval t ↘ a → ¬Tm n t → ¬Tm n a
  Eval-¬Tm eBound tm = tm
  Eval-¬Tm eFree tm = tm
  Eval-¬Tm eZero tm = tm
  Eval-¬Tm (eSucc e) (¬tmSucc tm) = ¬tmSucc (Eval-¬Tm e tm)
  Eval-¬Tm (eLam e) (¬tmLam tm) = ¬tmLam (Eval-¬Tm e tm)
  Eval-¬Tm (eApp e e₁ x) (¬tmApp₁ tm) = ●-¬Tm x (¬tmApp₁ (Eval-¬Tm e tm))
  Eval-¬Tm (eApp e e₁ x) (¬tmApp₂ x₁ tm) = ●-¬Tm x (inj-tmApp₂ (Eval-¬Tm e₁ tm))
  Eval-¬Tm (eRec e e₁ e₂ x) (¬tmRec₁ tm) = rec-¬Tm x (¬tmRec₁ (Eval-¬Tm e tm))
  Eval-¬Tm (eRec e e₁ e₂ x) (¬tmRec₂ x₁ tm) =
    rec-¬Tm x (inj-tmRec₂ (Eval-¬Tm e₁ tm))
  Eval-¬Tm (eRec e e₁ e₂ x) (¬tmRec₃ x₁ x₂ tm) =
    rec-¬Tm x (inj-tmRec₃ (Eval-¬Tm e₂ tm))

Eval-Tm' : ∀{t n a} → Eval t ↘ a → Tm n a → Tm n t
Eval-Tm' {t} {n} e tm with decTm n t
Eval-Tm' e tm | inj₁ x = x
Eval-Tm' e tm | inj₂ y = ⊥-elim (¬Tm-lemma (Eval-¬Tm e y) tm)

Eval-¬Tm' : ∀{t a n} → Eval t ↘ a → ¬Tm n a → ¬Tm n t
Eval-¬Tm' e ¬tm = ¬Tm-lemma' λ x → ¬Tm-lemma ¬tm (Eval-Tm x e)

mutual

  ●wk : ∀{t s a w} → t ● s ↘ a → wk t w ● wk s w ↘ wk a w
  ●wk {w = w} (●β (βrdx tmt tms) y)
    rewrite null-wk {w = w} tmt | null-wk {w = w} tms
          | null-wk {w = w} (Eval-Tm (sub-cover-lemma 0 0 tmt tms) y) =
    ●β (βrdx tmt tms) y
  ●wk {w = w} (●Ne x) = ●Ne (neWkLemma x)

  recwk : ∀{z s t a w}
        → Rec z · s · t ↘ a → Rec wk z w · wk s w · wk t w ↘ wk a w
  recwk {w = w} (rZ (NrdxZ tmz tms))
    rewrite null-wk {w = w} tmz | null-wk {w = w} tms =
            rZ (NrdxZ tmz tms)
  recwk {z} {s} {t} {a} {w} (rS (NrdxS {n = n} tmz tms tmn) r x₃ x₄)
    rewrite null-wk {w = w} tmz | null-wk {w = w} tms | null-wk {w = w} tmn =
            rS (NrdxS tmz tms tmn) r x₃ goal
    where
      aux = ●-Tm (●-Tm tms tmn x₃) (rec-Tm tmz tms tmn r) x₄
      goal : _ ● _ ↘ wk a w
      goal rewrite null-wk {w = w} aux = x₄
  recwk (rNe x) = rNe (neWkLemma x)

  wkEval : ∀{t s w} → Eval t ↘ s → Eval wk t w ↘ wk s w
  wkEval eBound = eBound
  wkEval eFree = eFree
  wkEval eZero = eZero
  wkEval (eSucc e) = eSucc (wkEval e)
  wkEval (eLam e) = eLam (wkEval e)
  wkEval (eApp e₁ e₂ x) = eApp (wkEval e₁) (wkEval e₂) (●wk x)
  wkEval (eRec e₁ e₂ e₃ x) = eRec (wkEval e₁) (wkEval e₂) (wkEval e₃) (recwk x)

sub-var-comm2 : ∀{s a b}
              → ∀ w n x
              → Eval wk (sub-var x (shift n (Id , a))) w ↘ b
              → Eval s ↘ a
              → Eval wk (sub-var x (shift n (Id , s))) w ↘ b
sub-var-comm2 w zero zero ex es
  with sym (Eval-fun (wkEval {w = w} (nfSelf (nfEval es))) ex)
sub-var-comm2 w zero zero ex es | refl = wkEval {w = w} es
sub-var-comm2 w zero (suc x) ex es = ex
sub-var-comm2 w (suc n) zero ex es = ex
sub-var-comm2 w (suc n) (suc x) ex es =
  ≡Eval (sym (wk-comp (Up Id) w _)) refl
    (sub-var-comm2 (Up Id ·ʷ w) n x (≡Eval (wk-comp (Up Id) w _) refl ex) es)

sub-comm2 : ∀{t s a b} → ∀ n
          → Eval sub t (shift n (Id , a)) ↘ b → Eval s ↘ a
          → Eval sub t (shift n (Id , s)) ↘ b
sub-comm2 {Free x} n eFree es = eFree
sub-comm2 {Bound x} n et es =
  ≡Eval (id-wk 0 _) refl (sub-var-comm2 Id n x
    (≡Eval (sym (id-wk 0 _)) refl et) es)
sub-comm2 {Lam t} n (eLam et) es = eLam (sub-comm2 {t} (suc n) et es)
sub-comm2 {t · s} n (eApp et et₁ x) es =
  eApp (sub-comm2 {t} n et es) (sub-comm2 {s} n et₁ es) x
sub-comm2 {Zero} n et es = et
sub-comm2 {Succ t} n (eSucc et) es = eSucc (sub-comm2 {t} n et es)
sub-comm2 {Rec z s t} n (eRec et et₁ et₂ x) es =
  eRec (sub-comm2 {z} n et es) (sub-comm2 {s} n et₁ es)
    (sub-comm2 {t} n et₂ es) x
