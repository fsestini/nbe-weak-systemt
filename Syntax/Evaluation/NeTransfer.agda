module Syntax.Evaluation.NeTransfer where

open import Syntax.Evaluation.Evaluation
open import Syntax.Raw
open import Syntax.Evaluation.NormalForm
open import Syntax.Evaluation.Properties

NeTransport : ∀{t σ a b} → Eval sub b σ ↘ a → Eval t ↘ b → Ne a → Ne b
NeTransport x eb ne with nfEval eb
NeTransport (eLam x) eb () | nfLam w
NeTransport eZero eb () | nfZero
NeTransport (eSucc x) eb () | nfSucc w
NeTransport _ _ _ | nfNe x = x

NeAppTransferLemma : ∀{t t' t'' s s' s'' σ}
  → Eval sub t'' σ ↘ t' → Eval sub s'' σ ↘ s'
  → Eval t ↘ t'' → Eval s ↘ s''
  → Ne (t' · s')
  → Ne (t'' · s'')
NeAppTransferLemma et es et' es' (neApp ne x x₁ x₂) = 
  inj-neApp (NeTransport et et' ne) (nfEval es')
NeAppTransferLemma et es et' es' (neApp₁ x x₁ x₂) = 
  neApp₁ (nfEval et') (nfEval es') (¬Sz-sub-lemma 0 (Eval-¬Sz' et x₂))
NeAppTransferLemma et es et' es' (neApp₂ x x₁ x₂ x₃) = 
  inj-neApp₂ (nfEval et') (nfEval es') (¬Sz-sub-lemma 0 (Eval-¬Sz' es x₃))

NeRecTransferLemma : ∀{z z' z'' s s' s'' t t' t'' σ}
  → Eval sub z'' σ ↘ z' → Eval sub s'' σ ↘ s' → Eval sub t'' σ ↘ t'
  → Eval z ↘ z'' → Eval s ↘ s'' → Eval t ↘ t''
  → Ne (Rec z' s' t')
  → Ne (Rec z'' s'' t'')
NeRecTransferLemma ez es et ez' es' et' (neRec x x₁ ne x₂ x₃ x₄) = 
  inj-neRec (nfEval ez') (nfEval es') (NeTransport et et' ne)
NeRecTransferLemma ez es et ez' es' et' (neRec₁ x x₁ x₂ x₃) = 
  neRec₁ (nfEval ez') (nfEval es') (nfEval et') 
    (¬Sz-sub-lemma 0 (Eval-¬Sz' ez x₃))
NeRecTransferLemma ez es et ez' es' et' (neRec₂ x x₁ x₂ x₃ x₄) = 
  inj-neRec₂ (nfEval ez') (nfEval es') (nfEval et') 
    (¬Sz-sub-lemma 0 (Eval-¬Sz' es x₄))
NeRecTransferLemma ez es et ez' es' et' (neRec₃ x x₁ x₂ x₃ x₄ x₅) = 
  inj-neRec₃ (nfEval ez') (nfEval es') (nfEval et') 
    (¬Sz-sub-lemma 0 (Eval-¬Sz' et x₅))
