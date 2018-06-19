module Syntax.Raw.RawEquality where

open import Syntax.Raw.Term
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Utils
open import Data.Nat
open import Data.Empty

dec≡ : (t s : Term) → Dec (t ≡ s)
dec≡ (Free x) (Free y) with x ≟ y
dec≡ (Free x) (Free y) | yes p = yes (cong Free p)
dec≡ (Free x) (Free y) | no ¬p = no (λ { refl → ¬p refl })
dec≡ (Free x) (Bound y) = no (λ ())
dec≡ (Free x) (Lam s) = no (λ ())
dec≡ (Free x) (s · s₁) = no (λ ())
dec≡ (Free x) Zero = no (λ ())
dec≡ (Free x) (Succ s) = no (λ ())
dec≡ (Free x) (Rec s s₁ s₂) = no (λ ())
dec≡ (Bound x) (Free x₁) = no (λ ())
dec≡ (Bound x) (Bound y) with x ≟ y
dec≡ (Bound x) (Bound y) | yes p = yes (cong Bound p)
dec≡ (Bound x) (Bound y) | no ¬p = no (λ { refl → ¬p refl })
dec≡ (Bound x) (Lam s) = no (λ ())
dec≡ (Bound x) (s · s₁) = no (λ ())
dec≡ (Bound x) Zero = no (λ ())
dec≡ (Bound x) (Succ s) = no (λ ())
dec≡ (Bound x) (Rec s s₁ s₂) = no (λ ())
dec≡ (Lam t) (Free x) = no (λ ())
dec≡ (Lam t) (Bound x) = no (λ ())
dec≡ (Lam t) (Lam s) with dec≡ t s
dec≡ (Lam t) (Lam s) | yes p = yes (cong Lam p)
dec≡ (Lam t) (Lam s) | no ¬p = no (λ { refl → ¬p refl })
dec≡ (Lam t) (s · s₁) = no (λ ())
dec≡ (Lam t) Zero = no (λ ())
dec≡ (Lam t) (Succ s) = no (λ ())
dec≡ (Lam t) (Rec s s₁ s₂) = no (λ ())
dec≡ (t · t₁) (Free x) = no (λ ())
dec≡ (t · t₁) (Bound x) = no (λ ())
dec≡ (t · t₁) (Lam s) = no (λ ())
dec≡ (t · s) (t' · s') with dec≡ t t' | dec≡ s s'
dec≡ (t · s) (t' · s') | yes p | yes q = yes (cong₂ _·_ p q)
dec≡ (t · s) (t' · s') | yes p | no ¬p = no (λ { refl → ¬p refl })
dec≡ (t · s) (t' · s') | no ¬p | yes p = no (λ { refl → ¬p refl })
dec≡ (t · s) (t' · s') | no ¬p | no ¬q = no (λ { refl → ¬q refl })
dec≡ (t · t₁) Zero = no (λ ())
dec≡ (t · t₁) (Succ s) = no (λ ())
dec≡ (t · t₁) (Rec s s₁ s₂) = no (λ ())
dec≡ Zero (Free x) = no (λ ())
dec≡ Zero (Bound x) = no (λ ())
dec≡ Zero (Lam s) = no (λ ())
dec≡ Zero (s · s₁) = no (λ ())
dec≡ Zero Zero = yes refl
dec≡ Zero (Succ s) = no (λ ())
dec≡ Zero (Rec s s₁ s₂) = no (λ ())
dec≡ (Succ t) (Free x) = no (λ ())
dec≡ (Succ t) (Bound x) = no (λ ())
dec≡ (Succ t) (Lam s) = no (λ ())
dec≡ (Succ t) (s · s₁) = no (λ ())
dec≡ (Succ t) Zero = no (λ ())
dec≡ (Succ t) (Succ s) with dec≡ t s
dec≡ (Succ t) (Succ s) | yes p = yes (cong Succ p)
dec≡ (Succ t) (Succ s) | no ¬p = no (λ { refl → ¬p refl })
dec≡ (Succ t) (Rec s s₁ s₂) = no (λ ())
dec≡ (Rec t t₁ t₂) (Free x) = no (λ ())
dec≡ (Rec t t₁ t₂) (Bound x) = no (λ ())
dec≡ (Rec t t₁ t₂) (Lam s) = no (λ ())
dec≡ (Rec t t₁ t₂) (s · s₁) = no (λ ())
dec≡ (Rec t t₁ t₂) Zero = no (λ ())
dec≡ (Rec t t₁ t₂) (Succ s) = no (λ ())
dec≡ (Rec z s t) (Rec z' s' t') with dec≡ z z' | dec≡ s s' | dec≡ t t'
dec≡ (Rec z s t) (Rec z' s' t') | yes p | yes q | yes r = yes (cong₃ Rec p q r)
dec≡ (Rec z s t) (Rec z' s' t') | yes p | yes p₁ | no ¬p = no (λ { refl → ¬p refl })
dec≡ (Rec z s t) (Rec z' s' t') | yes p | no ¬p | yes p₁ = no (λ { refl → ¬p refl })
dec≡ (Rec z s t) (Rec z' s' t') | yes p | no ¬p | no ¬p₁ = no (λ { refl → ¬p₁ refl })
dec≡ (Rec z s t) (Rec z' s' t') | no ¬p | yes p | yes p₁ = no (λ { refl → ¬p refl })
dec≡ (Rec z s t) (Rec z' s' t') | no ¬p | yes p | no ¬p₁ = no (λ { refl → ¬p₁ refl })
dec≡ (Rec z s t) (Rec z' s' t') | no ¬p | no ¬p₁ | yes p = no (λ { refl → ¬p₁ refl })
dec≡ (Rec z s t) (Rec z' s' t') | no ¬p | no ¬p₁ | no ¬p₂ = no (λ { refl → ¬p₂ refl })
