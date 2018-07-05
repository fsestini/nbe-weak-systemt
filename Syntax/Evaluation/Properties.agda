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
  ●-Sz : ∀{t s a n} → Sz n t → Sz n s → t ● s ↘ a → Sz n a
  ●-Sz {n = n} tmt tms (●β (βrdx x x₂) x₁) =
    liftSz n (Eval-Sz (sub-cover-lemma 0 0 x x₂) x₁)
  ●-Sz tmt tms (●Ne x) = tmApp tmt tms

  rec-Sz : ∀{z s t a n} → Sz n z → Sz n s → Sz n t
         → Rec z · s · t ↘ a → Sz n a
  rec-Sz tmz tms tmt (rZ x) = tmz
  rec-Sz tmz tms (tmSucc tmt) (rS x r x₁ x₂) =
    ●-Sz (●-Sz tms tmt x₁) (rec-Sz tmz tms tmt r) x₂
  rec-Sz tmz tms tmt (rNe x) = tmRec tmz tms tmt

  Eval-Sz : ∀{t s n} → Sz n t → Eval t ↘ s → Sz n s
  Eval-Sz tmFree eFree = tmFree
  Eval-Sz (tmVar x₁) eBound = tmVar x₁
  Eval-Sz (tmLam tm) (eLam e) = tmLam (Eval-Sz tm e)
  Eval-Sz (tmApp tm tm₁) (eApp e e₁ x) = ●-Sz (Eval-Sz tm e) (Eval-Sz tm₁ e₁) x
  Eval-Sz tmZero eZero = tmZero
  Eval-Sz (tmSucc tm) (eSucc e) = tmSucc (Eval-Sz tm e)
  Eval-Sz (tmRec tm tm₁ tm₂) (eRec e e₁ e₂ x) =
    rec-Sz (Eval-Sz tm e) (Eval-Sz tm₁ e₁) (Eval-Sz tm₂ e₂) x

mutual

  ●-¬Sz : ∀{t s a n} → t ● s ↘ a → ¬Sz n (t · s) → ¬Sz n a
  ●-¬Sz (●β (βrdx x x₂) x₁) (¬tmApp₁ tm) =
    ⊥-elim (¬Sz-lemma tm (tmLam (liftSz _ x)))
  ●-¬Sz (●β (βrdx x x₃) x₁) (¬tmApp₂ x₂ tm) =
    ⊥-elim (¬Sz-lemma tm (liftSz _ x₃))
  ●-¬Sz (●Ne x) tm = tm

  rec-¬Sz : ∀{z s t n a} → Rec z · s · t ↘ a → ¬Sz n (Rec z s t) → ¬Sz n a
  rec-¬Sz (rZ (NrdxZ x x₁)) (¬tmRec₁ tm) = ⊥-elim (¬Sz-lemma tm (liftSz _ x))
  rec-¬Sz (rZ (NrdxZ x x₁)) (¬tmRec₂ x₂ tm) = ⊥-elim (¬Sz-lemma tm (liftSz _ x₁))
  rec-¬Sz (rZ (NrdxZ x x₁)) (¬tmRec₃ x₂ x₃ ())
  rec-¬Sz (rS (NrdxS x x₃ x₄) r x₁ x₂) (¬tmRec₁ tm) =
    ⊥-elim (¬Sz-lemma tm (liftSz _ x))
  rec-¬Sz (rS (NrdxS x x₃ x₄) r x₁ x₂) (¬tmRec₂ x₅ tm) =
    ⊥-elim (¬Sz-lemma tm (liftSz _ x₃))
  rec-¬Sz (rS (NrdxS x x₃ x₄) r x₁ x₂) (¬tmRec₃ x₅ x₆ (¬tmSucc tm)) =
    ⊥-elim (¬Sz-lemma tm (liftSz _ x₄))
  rec-¬Sz (rNe x) tm = tm

  Eval-¬Sz : ∀{t a n} → Eval t ↘ a → ¬Sz n t → ¬Sz n a
  Eval-¬Sz eBound tm = tm
  Eval-¬Sz eFree tm = tm
  Eval-¬Sz eZero tm = tm
  Eval-¬Sz (eSucc e) (¬tmSucc tm) = ¬tmSucc (Eval-¬Sz e tm)
  Eval-¬Sz (eLam e) (¬tmLam tm) = ¬tmLam (Eval-¬Sz e tm)
  Eval-¬Sz (eApp e e₁ x) (¬tmApp₁ tm) = ●-¬Sz x (¬tmApp₁ (Eval-¬Sz e tm))
  Eval-¬Sz (eApp e e₁ x) (¬tmApp₂ x₁ tm) = ●-¬Sz x (inj-tmApp₂ (Eval-¬Sz e₁ tm))
  Eval-¬Sz (eRec e e₁ e₂ x) (¬tmRec₁ tm) = rec-¬Sz x (¬tmRec₁ (Eval-¬Sz e tm))
  Eval-¬Sz (eRec e e₁ e₂ x) (¬tmRec₂ x₁ tm) =
    rec-¬Sz x (inj-tmRec₂ (Eval-¬Sz e₁ tm))
  Eval-¬Sz (eRec e e₁ e₂ x) (¬tmRec₃ x₁ x₂ tm) =
    rec-¬Sz x (inj-tmRec₃ (Eval-¬Sz e₂ tm))

Eval-Sz' : ∀{t n a} → Eval t ↘ a → Sz n a → Sz n t
Eval-Sz' {t} {n} e tm with decSz n t
Eval-Sz' e tm | inj₁ x = x
Eval-Sz' e tm | inj₂ y = ⊥-elim (¬Sz-lemma (Eval-¬Sz e y) tm)

Eval-¬Sz' : ∀{t a n} → Eval t ↘ a → ¬Sz n a → ¬Sz n t
Eval-¬Sz' e ¬tm = ¬Sz-lemma' λ x → ¬Sz-lemma ¬tm (Eval-Sz x e)

mutual

  ●wk : ∀{t s a w} → t ● s ↘ a → wk t w ● wk s w ↘ wk a w
  ●wk {w = w} (●β (βrdx tmt tms) y)
    rewrite null-wk {w = w} tmt | null-wk {w = w} tms
          | null-wk {w = w} (Eval-Sz (sub-cover-lemma 0 0 tmt tms) y) =
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
      aux = ●-Sz (●-Sz tms tmn x₃) (rec-Sz tmz tms tmn r) x₄
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
