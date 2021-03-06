\begin{code}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture07 where

import Lecture06
open Lecture06 public

-- Section 7.1 Fiberwise equivalences
tot : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → ((x : A) → B x → C x) → ( Σ A B → Σ A C)
tot f (dpair x y) = dpair x (f x y)

-- There is a function from the fibers of the induced map on total spaces, to the fibers of the fiberwise transformation
fib-ftr-fib-tot : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : (x : A) → B x → C x) → (t : Σ A C) → fib (tot f) t → fib (f (pr1 t)) (pr2 t)
fib-ftr-fib-tot f .(dpair x (f x y)) (dpair (dpair x y) refl) = dpair y refl

-- This function has a converse
fib-tot-fib-ftr : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : (x : A) → B x → C x) → (t : Σ A C) → fib (f (pr1 t)) (pr2 t) → fib (tot f) t
fib-tot-fib-ftr F (dpair a .(F a y)) (dpair y refl) = dpair (dpair a y) refl

issec-fib-tot-fib-ftr : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : (x : A) → B x → C x) → (t : Σ A C) → ((fib-ftr-fib-tot f t) ∘ (fib-tot-fib-ftr f t)) ~ id
issec-fib-tot-fib-ftr f (dpair x .(f x y)) (dpair y refl) = refl

isretr-fib-tot-fib-ftr : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : (x : A) → B x → C x) → (t : Σ A C) → ((fib-tot-fib-ftr f t) ∘ (fib-ftr-fib-tot f t)) ~ id
isretr-fib-tot-fib-ftr f .(dpair x (f x y)) (dpair (dpair x y) refl) = refl

-- We establish that the fibers of the induced map on total spaces are equivalent to the fibers of the fiberwise transformation.
is-equiv-fib-ftr-fib-tot : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : (x : A) → B x → C x) → (t : Σ A C) → is-equiv (fib-ftr-fib-tot f t)
is-equiv-fib-ftr-fib-tot f t =
  pair
    (dpair (fib-tot-fib-ftr f t) (issec-fib-tot-fib-ftr f t))
    (dpair (fib-tot-fib-ftr f t) (isretr-fib-tot-fib-ftr f t))

-- Any fiberwise equivalence induces an equivalence on total spaces
is-fiberwise-equiv : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → ((x : A) → B x → C x) → UU (i ⊔ (j ⊔ k))
is-fiberwise-equiv f = (x : _) → is-equiv (f x)

is-equiv-tot-is-fiberwise-equiv :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → is-fiberwise-equiv f →
  is-equiv (tot f )
is-equiv-tot-is-fiberwise-equiv f H =
  is-equiv-is-contr-map
    ( λ t → is-contr-is-equiv _
      ( fib-ftr-fib-tot f t)
      ( is-equiv-fib-ftr-fib-tot f t)
      ( is-contr-map-is-equiv (H _) (pr2 t)))

-- Conversely, any fiberwise transformation that induces an equivalence on total spaces is a fiberwise equivalence.
is-fiberwise-equiv-is-equiv-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → is-equiv (tot f) →
  is-fiberwise-equiv f
is-fiberwise-equiv-is-equiv-tot f H x =
  is-equiv-is-contr-map
    (λ z → is-contr-is-equiv' _
      (fib-ftr-fib-tot f (dpair x z))
      (is-equiv-fib-ftr-fib-tot f (dpair x z))
      (is-contr-map-is-equiv H (dpair x z)))

-- Section 7.2 The fundamental theorem

-- The general form of the fundamental theorem of identity types
id-fundamental-gen : {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) → is-contr (Σ A B) → (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f
id-fundamental-gen {_} {_} {A} {B} a b C f x =
  is-fiberwise-equiv-is-equiv-tot f
    (is-equiv-is-contr _ (is-contr-total-path A a) C) x

-- The canonical form of the fundamental theorem of identity types
id-fundamental : {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  is-contr (Σ A B) → is-fiberwise-equiv (ind-Id a (λ x p → B x) b)
id-fundamental {i} {j} {A} {B} a b H =
  id-fundamental-gen a b H (ind-Id a (λ x p → B x) b)

-- The converse of the fundamental theorem of identity types
id-fundamental' : {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  (is-fiberwise-equiv (ind-Id a (λ x p → B x) b)) → is-contr (Σ A B)
id-fundamental' {i} {j} {A} {B} a b H =
  is-contr-is-equiv' _
    (tot (ind-Id a (λ x p → B x) b))
    (is-equiv-tot-is-fiberwise-equiv _ H)
    (is-contr-total-path A a)

-- As an application we show that equivalences are embeddings.
is-emb : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-emb f = (x y : _) → is-equiv (ap f {x} {y})

is-emb-is-equiv : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → is-equiv f → is-emb f
is-emb-is-equiv {i} {j} {A} {B} f E x =
  id-fundamental-gen x refl
    (is-contr-is-equiv' _ (tot (λ y (p : Id (f y) (f x)) → inv p))
        (is-equiv-tot-is-fiberwise-equiv _ (λ y → is-equiv-inv (f y) (f x)))
      (is-contr-map-is-equiv E (f x)))
    (λ y p → ap f p)

-- Exercises

-- Exercise 7.1

tot-htpy : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k}
  {f g : (x : A) → B x → C x} → (H : (x : A) → f x ~ g x) → tot f ~ tot g
tot-htpy H = {!!}

tot-id : {i j : Level} {A : UU i} (B : A → UU j) →
  (tot (λ x (y : B x) → y)) ~ id
tot-id B = {!!}

tot-comp : {i j j' j'' : Level}
  {A : UU i} {B : A → UU j} {B' : A → UU j'} {B'' : A → UU j''}
  (f : (x : A) → B x → B' x) (g : (x : A) → B' x → B'' x) →
  tot (λ x → (g x) ∘ (f x)) ~ ((tot g) ∘ (tot f))
tot-comp f g  = {!!}

-- Exercise 7.2
fib' : {i j : Level} {A : UU i} {B : UU j} → (A → B) → B → UU (i ⊔ j)
fib' f y = {!!}

fib'-fib : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  fib f y → fib' f y
fib'-fib f y t = {!!}

is-equiv-fib'-fib : {i j : Level} {A : UU i} {B : UU j}
  (f : A → B) → is-fiberwise-equiv (fib'-fib f)
is-equiv-fib'-fib f y = {!!}

-- Exercise 7.3
is-equiv-top-is-equiv-bottom-square :
  {i j k l : Level} {A : UU i} {B : UU j} {C : UU k} {D : UU l}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  (is-equiv f) → (is-equiv g) → (is-equiv i) → (is-equiv h)
is-equiv-top-is-equiv-bottom-square f g h i H Ef Eg Ei = {!!}

is-equiv-bottom-is-equiv-top-square :
  {i j k l : Level} {A : UU i} {B : UU j} {C : UU k} {D : UU l}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  (is-equiv f) → (is-equiv g) → (is-equiv h) → (is-equiv i)
is-equiv-bottom-is-equiv-top-square f g h i H Ef Eg Eh = {!!}

fib-triangle : {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  (x : X) → (fib f x) → (fib g x)
fib-triangle f g h H x f-fib = {!!}

square-tot-fib-triangle : {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (h ∘ (Σ-fib-to-domain f)) ~
  ((Σ-fib-to-domain g) ∘ (tot (fib-triangle f g h H)))
square-tot-fib-triangle f g h H = {!!}

is-fiberwise-equiv-is-equiv-triangle : {i j k : Level}
  {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (E : is-equiv h) → is-fiberwise-equiv (fib-triangle f g h H)
is-fiberwise-equiv-is-equiv-triangle f g h H E = {!!}

is-equiv-triangle-is-fiberwise-equiv :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (E : is-fiberwise-equiv (fib-triangle f g h H)) → is-equiv h
is-equiv-triangle-is-fiberwise-equiv f g h H E = {!!}

-- Exercise 7.7
id-fundamental-retr : {i j : Level} {A : UU i} {B : A → UU j} (a : A) →
  (i : (x : A) → B x → Id a x) → (R : (x : A) → retr (i x)) →
  is-fiberwise-equiv i
id-fundamental-retr {_} {_} {A} {B} a i R = {!!}

-- Exercise 7.12

coherence-reduction-map : {i j : Level} {A : UU i} {B : A → UU j}
  (a : A) (α : (x : A) → B x → Id a x) →
  (Σ (B a) (λ b → Id (α a b) refl)) → Σ A B
coherence-reduction-map a α y = {!!}

equiv-idtypes-fam-in-id : {i j : Level} {A : UU i} {B : A → UU j}
  (a : A) (α : (x : A) → B x → Id a x) →
  {x : A} (p : Id a x) (b : B x) → (Id (α a (tr B (inv p) b)) refl) ≃ (Id (α x b) p)
equiv-idtypes-fam-in-id a α p b = {!!}

is-contr-coherence-reduction-map : {i j : Level} {A : UU i} {B : A → UU j}
  (a : A) (α : (x : A) → B x → Id a x) →
  is-contr-map (coherence-reduction-map a α)
is-contr-coherence-reduction-map {i} {j} {A} {B} a α z = {!!}

coherence-introduction-map : {i j : Level} {A : UU i} {B : A → UU j}
  (a : A) (α : (x : A) → B x → Id a x) →
  (Σ A B) → (Σ (B a) (λ b → Id (α a b) refl))
coherence-introduction-map a α (dpair x y) = {!!}

right-inverse-coherence-introduction-map :
  {i j : Level} {A : UU i} {B : A → UU j}
  (a : A) (α : (x : A) → B x → Id a x) →
  ((coherence-reduction-map a α) ∘ (coherence-introduction-map a α)) ~ id
right-inverse-coherence-introduction-map a α = {!!}

left-inverse-coherence-introduction-map :
  {i j : Level} {A : UU i} {B : A → UU j}
  (a : A) (α : (x : A) → B x → Id a x) →
  ((coherence-introduction-map a α) ∘ (coherence-reduction-map a α)) ~ id
left-inverse-coherence-introduction-map {i} {j} {A} {B} a α  = {!!}

\end{code}
