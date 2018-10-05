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
tr-concat refl q b = refl
--or...
-- tr-concat refl refl b = refl

-- Exercise 4.2
inv-assoc : {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z) → Id (inv (concat _ p q)) (concat _ (inv q) (inv p))
inv-assoc refl refl = refl

-- Exercise 4.3
tr-triv : {i j : Level} {A : UU i} {B : UU j} {x y : A} (p : Id x y) (b : B) → Id (tr (λ (a : A) → B) p b) b
tr-triv refl b = refl

apd-triv : {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A} (p : Id x y) → Id (apd f p) (concat (f x) (tr-triv p (f x)) (ap f p))
apd-triv f refl = refl

-- Exercise 4.4
tr-id-left-subst : {i j : Level} {A : UU i} {B : UU j} {f : A → B} {x y : A} (p : Id x y) (b : B) →
  (q : Id (f x) b) → Id (tr (λ (a : A) → Id (f a) b) p q) (concat _ (inv (ap f p)) q)
tr-id-left-subst refl b q = refl

tr-id-right-subst : {i j : Level} {A : UU i} {B : UU j} {f : A → B} {x y : A} (p : Id x y) (b : B) → (q : Id b (f x)) → Id (tr (λ (a : A) → Id b (f a)) p q) (concat _ q (ap f p))
tr-id-right-subst refl b refl = refl

-- Exercise 4.5
inv-con : {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z) (r : Id x z) → (Id (concat _ p q) r) → Id q (concat _ (inv p) r)
-- this solution relies on the particular choice of how we defined concat asymmetrically above
inv-con refl q r α = α

con-inv : {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z) (r : Id x z) → (Id (concat _ p q) r) → Id p (concat _ r (inv q))
con-inv refl q .q refl = inv (right-inv q)
-- or, of course, we can always to PIOEIS for both problems...
-- inv-con refl refl refl refl = refl
-- con-inv refl refl refl refl = refl

-- Exercise 4.6
lift : {i j : Level} {A : UU i} {B : A → UU j} {x y : A} (p : Id x y) (b : B x) → Id (dpair x b) (dpair y (tr B p b))
lift refl b = refl

-- Exercise 4.7
associative-add-ℕ : (x y z : ℕ) → Id (add-ℕ (add-ℕ x y) z) (add-ℕ x (add-ℕ y z))
associative-add-ℕ zero-ℕ y z = refl
associative-add-ℕ (succ-ℕ x) y z = ap succ-ℕ (associative-add-ℕ x y z)

right-unit-law-add-ℕ : (x : ℕ) → Id (add-ℕ x zero-ℕ) x
right-unit-law-add-ℕ zero-ℕ = refl
right-unit-law-add-ℕ (succ-ℕ x) = ap succ-ℕ (right-unit-law-add-ℕ x)

left-unit-law-add-ℕ : (x : ℕ) → Id (add-ℕ zero-ℕ x) x
left-unit-law-add-ℕ zero-ℕ = refl
left-unit-law-add-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-add-ℕ x)

left-successor-law-add-ℕ : (x y : ℕ) → Id (add-ℕ (succ-ℕ x) y) (succ-ℕ (add-ℕ x y))
-- again we have a proof whose simplicity relies on a choice we've made previously in a definition
left-successor-law-add-ℕ x y = refl

right-successor-law-add-ℕ : (x y : ℕ) → Id (add-ℕ x (succ-ℕ y)) (succ-ℕ (add-ℕ x y))
right-successor-law-add-ℕ zero-ℕ y = refl
right-successor-law-add-ℕ (succ-ℕ x) y = ap succ-ℕ (right-successor-law-add-ℕ x y)

commutative-add-ℕ : (x y : ℕ) → Id (add-ℕ x y) (add-ℕ y x)
commutative-add-ℕ zero-ℕ y = inv (right-unit-law-add-ℕ y)
commutative-add-ℕ (succ-ℕ x) y = concat (succ-ℕ (add-ℕ y x)) ((ap succ-ℕ (commutative-add-ℕ x y))) ((inv (right-successor-law-add-ℕ y x)))

right-unit-law-mul-ℕ : (x : ℕ) → Id (mul-ℕ x one-ℕ) x
right-unit-law-mul-ℕ zero-ℕ = refl
right-unit-law-mul-ℕ (succ-ℕ x) = concat _ (right-successor-law-add-ℕ (mul-ℕ x one-ℕ) zero-ℕ) ((ap succ-ℕ ((concat _ (right-unit-law-add-ℕ (mul-ℕ x one-ℕ)) (right-unit-law-mul-ℕ x)))))

left-unit-law-mul-ℕ : (x : ℕ) → Id (mul-ℕ one-ℕ x) x
left-unit-law-mul-ℕ x = refl

left-successor-law-mul-ℕ : (x y : ℕ) → Id (mul-ℕ (succ-ℕ x) y) (add-ℕ (mul-ℕ x y) y)
left-successor-law-mul-ℕ x y = refl

right-successor-law-mul-ℕ : (x y : ℕ) → Id (mul-ℕ x (succ-ℕ y)) (add-ℕ x (mul-ℕ x y))
right-successor-law-mul-ℕ zero-ℕ y = refl
right-successor-law-mul-ℕ (succ-ℕ x) y =
  concat _
    (right-successor-law-add-ℕ (mul-ℕ x (succ-ℕ y)) y)
    ((ap succ-ℕ
      (concat _
        ( ap (λ z → add-ℕ z y) (right-successor-law-mul-ℕ x y) )
        (associative-add-ℕ x (mul-ℕ x y) y))))

left-distributive-mul-add-ℕ : (x y z : ℕ) → Id (mul-ℕ x (add-ℕ y z)) (add-ℕ (mul-ℕ x y) (mul-ℕ x z))
left-distributive-mul-add-ℕ zero-ℕ y z = refl
left-distributive-mul-add-ℕ (succ-ℕ x) y z = --WTS (S x)(y+z) = (S x)y + (S x)z which is automatically rewritten to x(y+z) + (y +z) = (xy + y) + (xz +z)
  concat _ (ap (λ w → (add-ℕ w (add-ℕ y z))) ( left-distributive-mul-add-ℕ x y z) ) -- x(y+z) + (y+z) = (xy + xz) + (y+z)
    (concat _ (associative-add-ℕ (mul-ℕ x y) (mul-ℕ x z) (add-ℕ y z)) -- ... = xy + (xz + (y+z))
      (concat _ (ap (λ w → (add-ℕ (mul-ℕ x y) w)) (inv (associative-add-ℕ (mul-ℕ x z) y z))) -- ... = xy + ((xz + y) + z)
        (concat _ (ap (λ w → (x ** y) + (w + z)) (commutative-add-ℕ (x ** z) y)) -- ... = xy + ((y + xz) + z)
          (concat _ (ap (λ w → (x ** y) + w)  (associative-add-ℕ y (x ** z) z) ) -- ... = xy + (y + (xz +z))
          (inv (associative-add-ℕ (x ** y) y ((x ** z) + z)))))) -- ... = (xy + y) + (xz + z)
      )
  
left-zero-law-mul-ℕ : (x : ℕ) → Id (mul-ℕ zero-ℕ x) zero-ℕ
left-zero-law-mul-ℕ x = refl

right-zero-law-mul-ℕ : (x : ℕ) → Id (mul-ℕ x zero-ℕ) zero-ℕ
right-zero-law-mul-ℕ zero-ℕ = refl
right-zero-law-mul-ℕ (succ-ℕ x) = 
  concat _ (right-unit-law-add-ℕ (x ** zero-ℕ)) --after the definition is applied we WTS  x0 + 0 = 0 but x0 + 0 = x0
    (right-zero-law-mul-ℕ x) --... = 0 by induction

commutative-mul-ℕ : (x y : ℕ) → Id (mul-ℕ x y) (mul-ℕ y x)
commutative-mul-ℕ zero-ℕ y = inv (right-zero-law-mul-ℕ y)
commutative-mul-ℕ (succ-ℕ x) y = --WTS (xy + y = y (S x))
  concat _ (commutative-add-ℕ (x ** y) y) -- well xy + y = y + xy
    (concat _ ((ap (λ w → y + w)) (commutative-mul-ℕ x y))
    (inv (right-successor-law-mul-ℕ y x)) )

right-distributive-mul-add-ℕ : (x y z : ℕ) → Id (mul-ℕ (add-ℕ x y) z) (add-ℕ (mul-ℕ x z) (mul-ℕ y z))
right-distributive-mul-add-ℕ x y z =
  concat _ (commutative-mul-ℕ (x + y) z) -- (x + y)z = z(x + y)
    (concat _ (left-distributive-mul-add-ℕ z x y) -- ... = zx + zy
      (concat _ (ap (λ w → (z ** x) + w) (commutative-mul-ℕ z y))  -- ... = zx + yz
        (ap (λ w →  w + (y ** z)) (commutative-mul-ℕ z x)))) -- ... = xz + yz

associative-mul-ℕ : (x y z : ℕ) → Id (mul-ℕ (mul-ℕ x y) z) (mul-ℕ x (mul-ℕ y z))
associative-mul-ℕ zero-ℕ y z = refl
associative-mul-ℕ (succ-ℕ x) y z =  -- WTS that (xy + y)z = x(yz)+yz
  concat _ (right-distributive-mul-add-ℕ (x ** y) y z) -- (xy + y)z = (xy)z + yz
  (ap (λ w → w + (y ** z)) (associative-mul-ℕ x y z))  -- then we apply our inductive step

-- Exercise 4.8
-- we just make an infix operator for concat to make the pentagon definition readable...
_∙_ : {i : Level} {A : UU i} {x y z : A} → Id x y → Id y z → Id x z
p ∙ q = concat _ p q
pentagon : {i : Level} {A : UU i} {x1 x2 x3 x4 x5 : A}
  (p : Id x1 x2) (q : Id x2 x3) (r : Id x3 x4)
  (s : Id x4 x5) →
  let
    α1 = inv ( ap (λ t → t ∙ s) (assoc p q r))
    α2 = inv ( assoc p ( q ∙ r) s)
    α3 = inv ( ap (λ t → p ∙ t) (assoc q r s))
    α4 = inv ( assoc (p ∙ q) r s)
    α5 = inv ( assoc p q (r ∙ s))
  in
    Id (α1 ∙ (α2 ∙ α3)) (α4 ∙ α5)
pentagon refl refl r s = refl



\end{code}
