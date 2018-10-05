\begin{code}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture06 where

import Lecture05
open Lecture05 public

-- Section 6.1 Contractible types

is-contr : {i : Level} → UU i → UU i
is-contr A = Sigma A (λ a → (x : A) → Id a x)

center : {i : Level} {A : UU i} → is-contr A → A
center (dpair c C) = c

-- We make sure that the contraction is coherent in a straightforward way
contraction : {i : Level} {A : UU i} (H : is-contr A) →
  (const A A (center H) ~ id)
contraction (dpair c C) x = concat _ (inv (C c)) (C x)

coh-contraction : {i : Level} {A : UU i} (H : is-contr A) →
  Id (contraction H (center H)) refl
coh-contraction (dpair c C) = left-inv (C c)

ev-pt : {i j : Level} (A : UU i) (a : A) (B : A → UU j) → ((x : A) → B x) → B a
ev-pt A a B f = f a

sing-ind-is-contr : {i j : Level} (A : UU i) (H : is-contr A) (B : A → UU j) →
  B (center H) → (x : A) → B x
sing-ind-is-contr A H B b x = tr B (contraction H x) b

sing-comp-is-contr : {i j : Level} (A : UU i) (H : is-contr A) (B : A → UU j) →
  (((ev-pt A (center H) B) ∘ (sing-ind-is-contr A H B)) ~ id)
sing-comp-is-contr A H B b =
  ap (λ (ω : Id (center H) (center H)) → tr B ω b) (coh-contraction H)

is-sing-is-contr : {i j : Level} (A : UU i) (H : is-contr A) (B : A → UU j) →
  sec (ev-pt A (center H) B)
is-sing-is-contr A H B =
  dpair (sing-ind-is-contr A H B) (sing-comp-is-contr A H B)

is-sing : {i : Level} (A : UU i) → A → UU (lsuc i)
is-sing {i} A a = (B : A → UU i) → sec (ev-pt A a B)

is-contr-is-sing : {i : Level} (A : UU i) (a : A) →
  is-sing A a → is-contr A
is-contr-is-sing A a S = dpair a (pr1 (S (λ y → Id a y)) refl)

is-sing-unit : is-sing unit star
is-sing-unit B = dpair ind-unit (λ b → refl)

is-contr-unit : is-contr unit
is-contr-unit = is-contr-is-sing unit star (is-sing-unit)

is-sing-total-path : {i : Level} (A : UU i) (a : A) →
  is-sing (Σ A (λ x → Id a x)) (dpair a refl)
is-sing-total-path A a B = dpair (ind-Σ ∘ (ind-Id a _)) (λ b → refl)

is-contr-total-path : {i : Level} (A : UU i) (a : A) →
  is-contr (Σ A (λ x → Id a x))
is-contr-total-path A a = is-contr-is-sing _ _ (is-sing-total-path A a)

-- Section 6.2 Contractible maps

fib : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (b : B) → UU (i ⊔ j)
fib f b = Σ _ (λ x → Id (f x) b)

is-contr-map : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-contr-map f = (y : _) → is-contr (fib f y)

-- Our goal is to show that contractible maps are equivalences.
-- First we construct the inverse of a contractible map.
inv-is-contr-map : {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-contr-map f → B → A
inv-is-contr-map H y = pr1 (center (H y))

-- Then we show that the inverse is a section.
issec-is-contr-map : {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (H : is-contr-map f) → (f ∘ (inv-is-contr-map H)) ~ id
issec-is-contr-map H y = pr2 (center (H y))

-- Then we show that the inverse is also a retraction.
isretr-is-contr-map : {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (H : is-contr-map f) → ((inv-is-contr-map H) ∘ f) ~ id
isretr-is-contr-map {_} {_} {A} {B} {f} H x =
  ap {_} {_} {fib f (f x)} {A} pr1
    { dpair (inv-is-contr-map H (f x)) (issec-is-contr-map H (f x))}
    { dpair x refl}
    ( concat
      ( center (H (f x)))
      ( inv
        ( contraction
          ( H (f x))
          ( dpair
            ( inv-is-contr-map H (f x)) (issec-is-contr-map H (f x)))))
            ( contraction (H (f x)) (dpair x refl)))

-- Finally we put it all together to show that contractible maps are equivalences.
is-equiv-is-contr-map : {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-contr-map f → is-equiv f
is-equiv-is-contr-map H =
  pair
    (dpair (inv-is-contr-map H) (issec-is-contr-map H))
    (dpair (inv-is-contr-map H) (isretr-is-contr-map H))

-- Section 6.3 Equivalences are contractible maps

htpy-nat : {i j : Level} {A : UU i} {B : UU j} {f g : A → B} (H : f ~ g)
  {x y : A} (p : Id x y) →
  Id (concat _ (H x) (ap g p)) (concat _ (ap f p) (H y))
htpy-nat H refl = right-unit (H _)

left-unwhisk : {i : Level} {A : UU i} {x y z : A} (p : Id x y) {q r : Id y z} →
  Id (concat _ p q) (concat _ p r) → Id q r
left-unwhisk refl s = concat _ (inv (left-unit _)) (concat _ s (left-unit _))

right-unwhisk : {i : Level} {A : UU i} {x y z : A} {p q : Id x y}
  (r : Id y z) → Id (concat _ p r) (concat _ q r) → Id p q
right-unwhisk refl s = concat _ (inv (right-unit _)) (concat _ s (right-unit _))

htpy-red : {i : Level} {A : UU i} {f : A → A} (H : f ~ id) →
  (x : A) → Id (H (f x)) (ap f (H x))
htpy-red {_} {A} {f} H x = right-unwhisk (H x)
  (concat (concat (f x) (H (f x)) (ap id (H x)))
    (ap (concat (f x) (H (f x))) (inv (ap-id (H x)))) (htpy-nat H (H x)))

center-is-invertible : {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-invertible f → (y : B) → fib f y
center-is-invertible {i} {j} {A} {B} {f}
  (dpair g (dpair issec isretr)) y =
    (dpair (g y)
      (concat _
        (inv (ap (f ∘ g) (issec y)))
        (concat _ (ap f (isretr (g y))) (issec y))))

mv-left : {i : Level} {A : UU i} {x y z : A}
  (p : Id x y) {q : Id y z} {r : Id x z} →
  Id (concat _ p q) r → Id q (concat _ (inv p) r)
mv-left refl s = s

square : {i : Level} {A : UU i} {x y1 y2 z : A}
  (p1 : Id x y1) (q1 : Id y1 z) (p2 : Id x y2) (q2 : Id y2 z) → UU i
square p q p' q' = Id (concat _ p q) (concat _ p' q')

sq-left-whisk : {i : Level} {A : UU i} {x y1 y2 z : A} {p1 p1' : Id x y1}
  (s : Id p1 p1') {q1 : Id y1 z} {p2 : Id x y2} {q2 : Id y2 z} →
  square p1 q1 p2 q2 → square p1' q1 p2 q2
sq-left-whisk refl sq = sq

sq-top-whisk : {i : Level} {A : UU i} {x y1 y2 z : A}
  {p1 : Id x y1} {q1 : Id y1 z}
  {p2 p2' : Id x y2} (s : Id p2 p2') {q2 : Id y2 z} →
  square p1 q1 p2 q2 → square p1 q1 p2' q2
sq-top-whisk refl sq = sq

contraction-is-invertible : {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (I : is-invertible f) → (y : B) → (t : fib f y) →
  Id (center-is-invertible I y) t
contraction-is-invertible {i} {j} {A} {B} {f}
  ( dpair g (dpair issec isretr)) y (dpair x refl) =
  eq-pair (dpair
    ( isretr x)
    ( concat _
      ( tr-id-left-subst (isretr x) (f x)
        ( pr2 (center-is-invertible
          ( dpair g (dpair issec isretr))
          ( f x))))
      ( inv (mv-left (ap f (isretr x))
        ( concat _
          ( right-unit (ap f (isretr x)))
          ( mv-left
            ( ap (f ∘ g) (issec y))
            ( sq-left-whisk
              {_} {_} {f(g(f(g(f x))))} {f(g(f x))} {f(g(f x))} {f x}
              { issec (f(g(f x)))} {ap (f ∘ g) (issec (f x))}
              ( htpy-red issec (f x))
              {ap f (isretr x)} {ap f (isretr (g (f x)))} { issec (f x)}
              ( sq-top-whisk
                {_} {_} {f(g(f(g(f x))))} {f(g(f x))} {f(g(f x))} {f x}
                { issec (f(g(f x)))} {_} {_} {_}
                ( concat _
                  ( ap-comp f (g ∘ f) (isretr x))
                  ( inv (ap (ap f) (htpy-red isretr x))))
                ( htpy-nat (htpy-right-whisk issec f) (isretr x))))))))))

is-contr-map-is-invertible : {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-invertible f → is-contr-map f
is-contr-map-is-invertible {i} {j} {A} {B} {f} I y =
    dpair (center-is-invertible I y) (contraction-is-invertible I y)

is-contr-map-is-equiv : {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-equiv f → is-contr-map f
is-contr-map-is-equiv = is-contr-map-is-invertible ∘ is-invertible-is-equiv

is-contr-total-path' : {i : Level} (A : UU i) (a : A) →
  is-contr (Σ A (λ x → Id x a))
is-contr-total-path' A a = is-contr-map-is-equiv (is-equiv-id _) a

-- Exercises

-- Exercise 6.1
is-prop-is-contr : {i : Level} {A : UU i} → is-contr A →
  (x y : A) → is-contr (Id x y)
is-prop-is-contr {i} {A} C x y =  sing-ind-is-contr A C (λ a → is-contr (Id a y)) (dpair (contraction C y) (ind-Id (center C) (λ z path-a-to-z → Id (contraction C z) path-a-to-z) (coh-contraction C) y)) x

-- Exercise 6.2
is-contr-retract-of : {i j : Level} {A : UU i} (B : UU j) →
  A retract-of B → is-contr B → is-contr A
is-contr-retract-of B (dpair f (dpair f-retr f-is-retr)) (dpair B-center B-contraction) =
  let A-center = (f-retr B-center) in
    dpair A-center λ a → concat _ (ap f-retr (B-contraction (f a))) (f-is-retr a)

-- Exercise 6.3
is-equiv-const-is-contr : {i : Level} {A : UU i} →
  is-contr A → is-equiv (const A unit star)
is-equiv-const-is-contr {i} {A} (dpair A-center A-contr) = pair (dpair (const unit A A-center) (λ a → contraction is-contr-unit a)) (dpair (const unit A A-center) A-contr)

is-contr-is-equiv-const : {i : Level} {A : UU i} →
  is-equiv (const A unit star) → is-contr A
is-contr-is-equiv-const (dpair (dpair const-sec sec-id) (dpair const-retr retr-id)) = dpair (const-retr star) λ a → retr-id a

-- TODO (Rennie): make more elegant
is-contr-is-equiv : {i j : Level} {A : UU i} (B : UU j) (f : A → B) →
  is-equiv f → is-contr B → is-contr A
is-contr-is-equiv B f Ef C = 
  let b = center C
      f-inv = pr1 (is-invertible-is-equiv Ef)
      f-left-inv-id = pr2 (pr2 ( is-invertible-is-equiv Ef ))
      a = f-inv b
  in
    dpair a (htpy-concat _ (htpy-left-whisk f-inv (htpy-right-whisk (contraction C) f)) f-left-inv-id)

is-contr-is-equiv' : {i j : Level} (A : UU i) {B : UU j} (f : A → B) →
  is-equiv f → is-contr A → is-contr B
is-contr-is-equiv' A f Ef C = 
  let
    a = center C
    f-inv = pr1 (is-invertible-is-equiv Ef)
    f-right-inv-id = pr1 (pr2 (is-invertible-is-equiv Ef))
    b = f a
  in
    dpair b (htpy-concat _ (htpy-left-whisk f (htpy-right-whisk (contraction C) f-inv)) f-right-inv-id)



is-equiv-is-contr : {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  is-contr A → is-contr B → is-equiv f
is-equiv-is-contr {i} {j} {A} {B} f CA CB =
  let
    A-to-pt-is-equiv = ( is-equiv-const-is-contr CA)
    pt-to-B = inv-is-equiv (is-equiv-const-is-contr CB)
    pt-to-B-is-equiv = is-equiv-inv-is-equiv (is-equiv-const-is-contr CB)
  in 
    is-equiv-comp f pt-to-B (const A unit star) (λ x → concat _ (inv ((contraction CB) (f x))) ((contraction CB) (pt-to-B star))) A-to-pt-is-equiv pt-to-B-is-equiv

-- Exercise 6.4
left-unit-law-Σ-map : {i j : Level} {C : UU i} (B : C → UU j)
  (H : is-contr C) → B (center H) → Σ C B
left-unit-law-Σ-map B H y = dpair (center H) y

left-unit-law-Σ-map-conv : {i j : Level} {C : UU i} (B : C → UU j)
  (H : is-contr C) → Σ C B → B (center H)
left-unit-law-Σ-map-conv B H (dpair x y) = inv-tr B ((contraction H) x) y

left-inverse-left-unit-law-Σ-map-conv : {i j : Level} {C : UU i}
  (B : C → UU j) (H : is-contr C) →
  ((left-unit-law-Σ-map-conv B H) ∘ (left-unit-law-Σ-map B H)) ~ id
-- left-inverse-left-unit-law-Σ-map-conv B H y = inv {!pair-eq  ? ?!}
left-inverse-left-unit-law-Σ-map-conv B H y = ap (λ w → inv-tr B w y) (coh-contraction H)

right-inverse-left-unit-law-Σ-map-conv : {i j : Level} {C : UU i}
  (B : C → UU j) (H : is-contr C) →
  ((left-unit-law-Σ-map B H) ∘ (left-unit-law-Σ-map-conv B H)) ~ id
right-inverse-left-unit-law-Σ-map-conv B H (dpair x y) =
  eq-pair
    (dpair
      ((contraction H) x)
      ((right-inv-inv-tr B (contraction H x)) y))

is-equiv-left-unit-law-Σ-map : {i j : Level} {C : UU i}
  (B : C → UU j) (H : is-contr C) → is-equiv (left-unit-law-Σ-map B H)
is-equiv-left-unit-law-Σ-map B H = pair (dpair (left-unit-law-Σ-map-conv B H) (right-inverse-left-unit-law-Σ-map-conv B H)) (dpair (left-unit-law-Σ-map-conv B H) (left-inverse-left-unit-law-Σ-map-conv B H))

left-unit-law-Σ : {i j : Level} {C : UU i} (B : C → UU j) (H : is-contr C) →
  B (center H) ≃ Σ C B
left-unit-law-Σ B H = dpair (left-unit-law-Σ-map B H) (is-equiv-left-unit-law-Σ-map B H)

-- Exercise 6.5
tr-fiber : {i j : Level} {A : UU i} {B : UU j}
  (f : A → B) {x y : B} (p : Id x y) (a : A) (q : Id (f a) x) →
  Id (tr (fib f) p (dpair a q)) (dpair a (concat x q p))
tr-fiber f refl a q = ap (dpair a) (inv (right-unit q) )
-- or just
-- tr-fiber f refl a refl = refl

-- Exercise 6.6
Σ-fib-to-domain : {i j : Level} {A : UU i} {B : UU j} (f : A → B ) →
  (Σ B (fib f)) → A
Σ-fib-to-domain f (dpair b (dpair a p)) = a

triangle-Σ-fib-to-domain : {i j : Level} {A : UU i} {B : UU j} (f : A → B ) →
  pr1 ~ (f ∘ (Σ-fib-to-domain f))
triangle-Σ-fib-to-domain f (dpair b (dpair a p))= inv p

domain-to-Σ-fib : {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  A → Σ B (fib f)
domain-to-Σ-fib f a = dpair (f a) (dpair a refl)

left-inverse-domain-to-Σ-fib : {i j : Level} {A : UU i} {B : UU j}
  (f : A → B ) → ((domain-to-Σ-fib f) ∘ (Σ-fib-to-domain f)) ~ id
left-inverse-domain-to-Σ-fib f (dpair .(f a) (dpair a refl)) = refl

right-inverse-domain-to-Σ-fib : {i j : Level} {A : UU i} {B : UU j}
  (f : A → B ) → ((Σ-fib-to-domain f) ∘ (domain-to-Σ-fib f)) ~ id
right-inverse-domain-to-Σ-fib f a = refl

is-equiv-Σ-fib-to-domain : {i j : Level} {A : UU i} {B : UU j}
  (f : A → B ) → is-equiv (Σ-fib-to-domain f)
is-equiv-Σ-fib-to-domain f = pair (dpair (domain-to-Σ-fib f ) (right-inverse-domain-to-Σ-fib f)) (dpair (domain-to-Σ-fib f) (left-inverse-domain-to-Σ-fib f))

equiv-Σ-fib-to-domain : {i j : Level} {A : UU i} {B : UU j}
  (f : A → B ) → Σ B (fib f) ≃ A
equiv-Σ-fib-to-domain f = dpair (Σ-fib-to-domain f) (is-equiv-Σ-fib-to-domain f)

-- Exercise 6.7
is-contr-left-factor-prod : {i j : Level} (A : UU i) (B : UU j) →
  is-contr (A × B) → is-contr A
is-contr-left-factor-prod A B H = is-contr-retract-of (A × B) (dpair (λ a → (pair a (pr2 (center H)))) (dpair pr1 λ x → refl)) H
-- is-contr-retract-of : {i j : Level} {A : UU i} (B : UU j) →
-- A retract-of B → is-contr B → is-contr A

is-contr-right-factor-prod : {i j : Level} (A : UU i) (B : UU j) →
  is-contr (A × B) → is-contr B
is-contr-right-factor-prod A B H = is-contr-retract-of (A × B) (dpair (λ b → (pair (pr1 (center H)) b)) (dpair pr2 (λ x → refl))) H

-- Exercise 6.8
-- Given any family B over A, there is a map from the fiber of the projection map (pr1 : Σ A B → A) to the type (B a), i.e. the fiber of B at a. In this exercise we define this map, and show that it is an equivalence, for every a : A.

fib-fam-fib-pr1 : {i j : Level} {A : UU i} (B : A → UU j)
  (a : A) → fib (pr1 {i} {j} {A} {B}) a → B a
fib-fam-fib-pr1 B a (dpair (dpair .a x₂) refl) = x₂

fib-pr1-fib-fam : {i j : Level} {A : UU i} (B : A → UU j)
  (a : A) → B a → fib (pr1 {i} {j} {A} {B}) a
fib-pr1-fib-fam B a b = dpair (dpair a b) refl

left-inverse-fib-pr1-fib-fam : {i j : Level} {A : UU i} (B : A → UU j)
  (a : A) → ((fib-pr1-fib-fam B a) ∘ (fib-fam-fib-pr1 B a)) ~ id
left-inverse-fib-pr1-fib-fam B a (dpair (dpair .a x₂) refl) = refl

right-inverse-fib-pr1-fib-fam : {i j : Level} {A : UU i} (B : A → UU j)
  (a : A) → ((fib-fam-fib-pr1 B a) ∘ (fib-pr1-fib-fam B a)) ~ id
right-inverse-fib-pr1-fib-fam B a y = refl

is-equiv-fib-fam-fib-pr1 : {i j : Level} {A : UU i} (B : A → UU j)
  (a : A) → is-equiv (fib-fam-fib-pr1 B a)
is-equiv-fib-fam-fib-pr1 B a = pair (dpair (fib-pr1-fib-fam B a) (right-inverse-fib-pr1-fib-fam B a)) (dpair (fib-pr1-fib-fam B a) (left-inverse-fib-pr1-fib-fam B a))

is-equiv-pr1-is-contr : {i j : Level} {A : UU i} (B : A → UU j) →
  ((a : A) → is-contr (B a)) → is-equiv (pr1 {i} {j} {A} {B})
is-equiv-pr1-is-contr B H = pair (dpair (λ a → dpair a (center (H a))) (λ w → refl)) (dpair (λ a → dpair a (center (H a))) λ a → eq-pair (dpair refl ((contraction (H (pr1 a))) (pr2 a))))

is-contr-is-equiv-pr1 : {i j : Level} {A : UU i} (B : A → UU j) →
  (is-equiv (pr1 {i} {j} {A} {B})) → ((a : A) → is-contr (B a))
is-contr-is-equiv-pr1 B pr1-is-equiv a = is-contr-is-equiv' (fib pr1 a) (fib-fam-fib-pr1 B a) (is-equiv-fib-fam-fib-pr1 B a) (is-contr-map-is-equiv pr1-is-equiv a)
-- is-contr-is-equiv-pr1 B (dpair (dpair x x₁) (dpair x₂ x₃)) a = dpair (fib-fam-fib-pr1 B a (dpair (x a) ((x₁ a)) )) λ y → {!!}

right-unit-law-Σ : {i j : Level} {A : UU i} (B : A → UU j) →
  ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
right-unit-law-Σ B H = dpair pr1 (is-equiv-pr1-is-contr B H)

\end{code}
