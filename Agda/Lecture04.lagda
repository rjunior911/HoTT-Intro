\begin{code}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture04 where

import Lecture03
open Lecture03 public

data Id {i : Level} {A : UU i} (x : A) : A → UU i where
  refl : Id x x

ind-Id : {i j : Level} {A : UU i} (x : A) (B : (y : A) (p : Id x y) → UU j) →
  (B x refl) → (y : A) (p : Id x y) → B y p
ind-Id x B b y refl = b

inv : {i : Level} {A : UU i} {x y : A} → Id x y → Id y x
inv (refl) = refl

concat : {i : Level} {A : UU i} {x : A} (y : A) {z : A} → Id x y → Id y z → Id x z
concat x refl q = q

assoc : {i : Level} {A : UU i} {x y z w : A} (p : Id x y) (q : Id y z) (r : Id z w) → Id (concat _ p (concat _ q r)) (concat _ (concat _ p q) r)
assoc refl q r = refl

left-unit : {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (concat _ refl p) p
left-unit p = refl

right-unit : {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (concat _ p refl) p
right-unit refl = refl

left-inv : {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id (concat _ (inv p) p) refl
left-inv refl = refl

right-inv : {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id (concat _ p (inv p)) refl
right-inv refl = refl

ap : {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A} (p : Id x y) → Id (f x) (f y)
ap f refl = refl

ap-id : {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (ap id p) p
ap-id refl = refl

ap-comp : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} (g : B → C) (f : A → B) {x y : A} (p : Id x y) → Id (ap (comp g f) p) (ap g (ap f p))
ap-comp g f refl = refl

ap-refl : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (x : A) →
  Id (ap f (refl {_} {_} {x})) refl
ap-refl f x = refl

ap-concat : {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y z : A} (p : Id x y) (q : Id y z) → Id (ap f (concat _ p q)) (concat _ (ap f p) (ap f q))
ap-concat f refl q = refl

ap-inv : {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A} (p : Id x y) → Id (ap f (inv p)) (inv (ap f p))
ap-inv f refl = refl

tr : {i j : Level} {A : UU i} (B : A → UU j) {x y : A} (p : Id x y) (b : B x) → B y
tr B refl b = b

apd : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) {x y : A} (p : Id x y) → Id (tr B p (f x)) (f y)
apd f refl = refl

-- Exercise 4.1
tr-concat : {i j : Level} {A : UU i} {B : A → UU j} {x y : A} (p : Id x y) {z : A} (q : Id y z) (b : B x) → Id (tr B q (tr B p b)) (tr B (concat y p q) b)
tr-concat p q b = {!!}

-- Exercise 4.2
inv-assoc : {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z) → Id (inv (concat _ p q)) (concat _ (inv q) (inv p))
inv-assoc p q = {!!}

-- Exercise 4.3
tr-triv : {i j : Level} {A : UU i} {B : UU j} {x y : A} (p : Id x y) (b : B) → Id (tr (λ (a : A) → B) p b) b
tr-triv p b = {!!}

apd-triv : {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A} (p : Id x y) → Id (apd f p) (concat (f x) (tr-triv p (f x)) (ap f p))
apd-triv f p = {!!}

-- Exercise 4.4
tr-id-left-subst : {i j : Level} {A : UU i} {B : UU j} {f : A → B} {x y : A} (p : Id x y) (b : B) →
  (q : Id (f x) b) → Id (tr (λ (a : A) → Id (f a) b) p q) (concat _ (inv (ap f p)) q)
tr-id-left-subst refl b q = {!!}

tr-id-right-subst : {i j : Level} {A : UU i} {B : UU j} {f : A → B} {x y : A} (p : Id x y) (b : B) → (q : Id b (f x)) → Id (tr (λ (a : A) → Id b (f a)) p q) (concat _ q (ap f p))
tr-id-right-subst refl b q = {!!}

-- Exercise 4.5
inv-con : {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z) (r : Id x z) → (Id (concat _ p q) r) → Id q (concat _ (inv p) r)
inv-con refl q r s = {!!}

con-inv : {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z) (r : Id x z) → (Id (concat _ p q) r) → Id p (concat _ r (inv q))
con-inv p q r α = {!!}

-- Exercise 4.6
lift : {i j : Level} {A : UU i} {B : A → UU j} {x y : A} (p : Id x y) (b : B x) → Id (dpair x b) (dpair y (tr B p b))
lift p b = {!!}

-- Exercise 4.7
associative-add-ℕ : (x y z : ℕ) → Id (add-ℕ (add-ℕ x y) z) (add-ℕ x (add-ℕ y z))
associative-add-ℕ x y z = {!!}

right-unit-law-add-ℕ : (x : ℕ) → Id (add-ℕ x zero-ℕ) x
right-unit-law-add-ℕ x = {!!}

left-unit-law-add-ℕ : (x : ℕ) → Id (add-ℕ zero-ℕ x) x
left-unit-law-add-ℕ x = {!!}

left-successor-law-add-ℕ : (x y : ℕ) → Id (add-ℕ (succ-ℕ x) y) (succ-ℕ (add-ℕ x y))
left-successor-law-add-ℕ x y = {!!}

right-successor-law-add-ℕ : (x y : ℕ) → Id (add-ℕ x (succ-ℕ y)) (succ-ℕ (add-ℕ x y))
right-successor-law-add-ℕ x y = {!!}

commutative-add-ℕ : (x y : ℕ) → Id (add-ℕ x y) (add-ℕ y x)
commutative-add-ℕ x y = {!!}

right-unit-law-mul-ℕ : (x : ℕ) → Id (mul-ℕ x one-ℕ) x
right-unit-law-mul-ℕ x = {!!}

left-unit-law-mul-ℕ : (x : ℕ) → Id (mul-ℕ one-ℕ x) x
left-unit-law-mul-ℕ x = {!!}

left-successor-law-mul-ℕ : (x y : ℕ) → Id (mul-ℕ (succ-ℕ x) y) (add-ℕ (mul-ℕ x y) y)
left-successor-law-mul-ℕ x y = {!!}

right-successor-law-mul-ℕ : (x y : ℕ) → Id (mul-ℕ x (succ-ℕ y)) (add-ℕ x (mul-ℕ x y))
right-successor-law-mul-ℕ x y = {!!}

left-distributive-mul-add-ℕ : (x y z : ℕ) → Id (mul-ℕ x (add-ℕ y z)) (add-ℕ (mul-ℕ x y) (mul-ℕ x z))
left-distributive-mul-add-ℕ x y z = {!!}

left-zero-law-mul-ℕ : (x : ℕ) → Id (mul-ℕ zero-ℕ x) zero-ℕ
left-zero-law-mul-ℕ x = {!!}

right-zero-law-mul-ℕ : (x : ℕ) → Id (mul-ℕ x zero-ℕ) zero-ℕ
right-zero-law-mul-ℕ x = {!!}

commutative-mul-ℕ : (x y : ℕ) → Id (mul-ℕ x y) (mul-ℕ y x)
commutative-mul-ℕ x y = {!!}

right-distributive-mul-add-ℕ : (x y z : ℕ) → Id (mul-ℕ (add-ℕ x y) z) (add-ℕ (mul-ℕ x z) (mul-ℕ y z))
right-distributive-mul-add-ℕ x y z = {!!}

associative-mul-ℕ : (x y z : ℕ) → Id (mul-ℕ (mul-ℕ x y) z) (mul-ℕ x (mul-ℕ y z))
associative-mul-ℕ x y z = {!!}

\end{code}
