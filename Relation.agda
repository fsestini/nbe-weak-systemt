module Relation where

open import Data.Product

-- Reflexive transitive closure
data RTClo {A : Set} (_∼_ : A → A → Set) : A → A → Set where
  step* : ∀{x y} → x ∼ y → RTClo _∼_ x y
  refl* : ∀{x} → RTClo _∼_ x x
  trans* : ∀{x y z} → RTClo _∼_ x y → RTClo _∼_ y z → RTClo _∼_ x z

-- Conv : ∀{A} → (A → A → Set) → A → A → Set
-- Conv {A} _∼_ x y = Σ A λ z → x ∼ z × y ∼ z

-- step≋ : ∀{A} {_∼_ : A → A → Set} {x y : A} → x ∼ y → Conv (RTClo _∼_) x y
-- step≋ r = _ , step* r , refl*

-- refl≋ : ∀{A} {_∼_ : A → A → Set} {x : A} → Conv (RTClo _∼_) x x
-- refl≋ = _ , refl* , refl*

-- symm≋ : ∀{A} {_∼_ : A → A → Set} {x y : A} → Conv (RTClo _∼_) x y → Conv (RTClo _∼_) y x
-- symm≋ (_ , p , q) = _ , q , p

-- trans≋ : ∀{A} {_∼_ : A → A → Set} {x y z : A} 
--        → Conv (RTClo _∼_) x y → Conv (RTClo _∼_) y z
--        → Conv (RTClo _∼_) x z
-- trans≋ (_ , p , q) (_ , p' , q') = _ , {!!} , {!!}
