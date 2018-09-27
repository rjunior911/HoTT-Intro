\begin{code}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture03 where

import Lecture02
open Lecture02 public

data unit : U where
  star : unit
  
𝟙 = unit

ind-unit : {i : Level} {P : unit → UU i} → P star → ((x : unit) → P x)
ind-unit p star = p

data empty : U where

𝟘 = empty

ind-empty : {i : Level} {P : empty → UU i} → ((x : empty) → P x)
ind-empty ()

¬ : {i : Level} → UU i → UU i
¬ A = A → empty

data bool : U where
  true false : bool

data coprod {i j : Level} (A : UU i) (B : UU j) : UU (i ⊔ j)  where
  inl : A → coprod A B
  inr : B → coprod A B

data Sigma {i j : Level} (A : UU i) (B : A → UU j) : UU (i ⊔ j) where
  dpair : (x : A) → (B x → Sigma A B)

Σ = Sigma

ind-Σ : {i j k : Level} {A : UU i} {B : A → UU j} {C : Σ A B → UU k} →
  ((x : A) (y : B x) → C (dpair x y)) → ((t : Σ A B) → C t)
ind-Σ f (dpair x y) = f x y

pr1 : {i j : Level} {A : UU i} {B : A → UU j} → Sigma A B → A
pr1 (dpair a b) = a

pr2 : {i j : Level} {A : UU i} {B : A → UU j} → (t : Sigma A B) → B (pr1 t)
pr2 (dpair a b) = b

prod : {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
prod A B = Sigma A (λ a → B)

_×_ :  {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A × B = prod A B

pair : {i j : Level} {A : UU i} {B : UU j} → A → (B → prod A B)
pair a b = dpair a b

-- Pointed types
U-pt : Type
U-pt = Sigma U (λ X → X)
 
-- Graphs
Gph : Type
Gph = Sigma U (λ X → (X → X → U))

-- Reflexive graphs
rGph : Type
rGph = Sigma U (λ X → Sigma (X → X → U) (λ R → (x : X) → R x x))

-- Finite sets
Fin : ℕ → U 
Fin zero-ℕ = empty
Fin (succ-ℕ n) = coprod (Fin n) unit

-- Observational equality on the natural numbers
Eq-ℕ : ℕ → (ℕ → U)
Eq-ℕ zero-ℕ zero-ℕ = 𝟙
Eq-ℕ zero-ℕ (succ-ℕ n) = 𝟘
Eq-ℕ (succ-ℕ m) zero-ℕ = 𝟘
Eq-ℕ (succ-ℕ m) (succ-ℕ n) = Eq-ℕ m n

-- The integers
ℤ : U
ℤ = coprod ℕ (coprod unit ℕ)

-- Inclusion of the negative integers
in-neg : ℕ → ℤ
in-neg n = inl n

-- Negative one
neg-one-ℤ : ℤ
neg-one-ℤ = in-neg zero-ℕ

-- Zero
zero-ℤ : ℤ
zero-ℤ = inr (inl star)

-- One
one-ℤ : ℤ
one-ℤ = inr (inr zero-ℕ)

-- Inclusion of the positive integers
in-pos : ℕ → ℤ
in-pos n = inr (inr n)

ind-ℤ : {i : Level} (P : ℤ → UU i) → P neg-one-ℤ → ((n : ℕ) → P (inl n) → P (inl (succ-ℕ n))) → P zero-ℤ → P one-ℤ → ((n : ℕ) → P (inr (inr (n))) → P (inr (inr (succ-ℕ n)))) → (k : ℤ) → P k
ind-ℤ P p-1 p-S p0 p1 pS (inl zero-ℕ) = p-1
ind-ℤ P p-1 p-S p0 p1 pS (inl (succ-ℕ x)) = p-S x (ind-ℤ P p-1 p-S p0 p1 pS (inl x))
ind-ℤ P p-1 p-S p0 p1 pS (inr (inl star)) = p0
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr zero-ℕ)) = p1
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (succ-ℕ x))) = pS x (ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (x))))

succ-ℤ : ℤ → ℤ
succ-ℤ (inl zero-ℕ) = zero-ℤ
succ-ℤ (inl (succ-ℕ x)) = inl x
succ-ℤ (inr (inl star)) = one-ℤ
succ-ℤ (inr (inr x)) = inr (inr (succ-ℕ x))

-- Exercise 3.1
-- In this exercise we were asked to show that (A + ¬A) implies (¬¬A → A).
-- In other words, we get double negation elimination for the types that are decidable
dne-dec : {i : Level} (A : UU i) → (coprod A (¬ A)) → (¬ (¬ A) → A)
dne-dec A c = {!!}
-- Exercise 3.3
-- In this exercise we were asked to show that the observational equality on ℕ is an equivalence relation.
reflexive-Eq-ℕ : (n : ℕ) → Eq-ℕ n n
reflexive-Eq-ℕ n = {!!}

symmetric-Eq-ℕ : (m n : ℕ) → Eq-ℕ m n → Eq-ℕ n m
symmetric-Eq-ℕ m n p = {!!}

transitive-Eq-ℕ : (l m n : ℕ) → Eq-ℕ l m → Eq-ℕ m n → Eq-ℕ l n
transitive-Eq-ℕ l m n p q = {!!} 

-- Exercise 3.4
-- In this exercise we were asked to show that observational equality on the natural numbers is the least reflexive relation, in the sense that it implies all other reflexive relation. As we will see once we introduce the identity type, it follows that observationally equal natural numbers can be identified.

-- We first make an auxilary construction, where the relation is quantified over inside the scope of the variables n and m. This is to ensure that the inductive hypothesis is strong enough to make the induction go through.
least-reflexive-Eq-ℕ' : {i : Level} (n m : ℕ)
                     (R : ℕ → ℕ → UU i) (ρ : (n : ℕ) → R n n) → Eq-ℕ n m → R n m
least-reflexive-Eq-ℕ' n m R ρ p = {!!}

-- Now we solve the actual exercise by rearranging the order of the variables.
least-reflexive-Eq-ℕ : {i : Level} {R : ℕ → ℕ → UU i}
  (ρ : (n : ℕ) → R n n) → (n m : ℕ) → Eq-ℕ n m → R n m
least-reflexive-Eq-ℕ ρ n m p = {!!}

-- Exercise 3.5
-- In this exercise we were asked to show that any function on the natural numbers preserves observational equality. The quick solution uses the fact that observational equality is the least reflexive relation.
preserve_Eq-ℕ : (f : ℕ → ℕ) (n m : ℕ) → (Eq-ℕ n m) → (Eq-ℕ (f n) (f m))
preserve_Eq-ℕ f n m p = {!!}

-- Exercise 3.6
-- In this exercise we were asked to construct the relations ≤ and < on the natural numbers, and show basic properties about them.

-- Definition of ≤ 
leq-ℕ : ℕ → ℕ → U
leq-ℕ n m = {!!}

_≤_ = leq-ℕ

-- Definition of <
le-ℕ : ℕ → ℕ → U
le-ℕ  n m = {!!}

_<_ = le-ℕ

reflexive-leq-ℕ : (n : ℕ) → n ≤ n
reflexive-leq-ℕ n = {!!}

anti-reflexive-le-ℕ : (n : ℕ) → ¬ (n < n)
anti-reflexive-le-ℕ n = {!!}

transitive-leq-ℕ : (n m l : ℕ) → (n ≤ m) → (m ≤ l) → (n ≤ l)
transitive-leq-ℕ n m l p q = {!!}

transitive-le-ℕ : (n m l : ℕ) → (le-ℕ n m) → (le-ℕ m l) → (le-ℕ n l)
transitive-le-ℕ n m l p q = {!!}

succ-le-ℕ : (n : ℕ) → le-ℕ n (succ-ℕ n)
succ-le-ℕ n = {!!}

-- Exercise 3.7
-- With the construction of the divisibility relation we open the door to basic number theory.
divides : (d n : ℕ) → U
divides d n = {!!}

-- Exercise 3.8
-- In this exercise we were asked to construct observational equality on the booleans. This construction is analogous to, but simpler than, the construction of observational equality on the natural numbers.
Eq-𝟚 : bool → bool → U
Eq-𝟚 x y = {!!}

reflexive-Eq-𝟚 : (x : bool) → Eq-𝟚 x x
reflexive-Eq-𝟚 x = {!!}

least-reflexive-Eq-𝟚 : {i : Level}
  (R : bool → bool → UU i) (ρ : (x : bool) → R x x)
  (x y : bool) → Eq-𝟚 x y → R x y

least-reflexive-Eq-𝟚 R ρ x y p = {!!}
-- Exercise 3.9
-- In this exercise we were asked to show that 1 + 1 satisfies the induction principle of the booleans. In other words, type theory cannot distinguish the booleans from the type 1 + 1. We will see later that they are indeed equivalent types.
t0 : coprod unit unit
t0 = {!!}

t1 : coprod unit unit
t1 = {!!}

ind-coprod-unit-unit : {i : Level} {P : coprod unit unit → UU i} →
  P t0 → P t1 → (x : coprod unit unit) → P x
ind-coprod-unit-unit A B x = {!!}

-- Exercise 3.10
-- In this exercise we were asked to define the relations ≤ and < on the integers. As a criterion of correctness, we were then also asked to show that the type of all integers l satisfying k ≤ l satisfy the induction principle of the natural numbers.

leq-ℤ : ℤ → ℤ → U
leq-ℤ n m = {!!}

reflexive-leq-ℤ : (k : ℤ) → leq-ℤ k k
reflexive-leq-ℤ  k = {!!}

transitive-leq-ℤ : (k l m : ℤ) → leq-ℤ k l → leq-ℤ l m → leq-ℤ k m
transitive-leq-ℤ k l m p q = {!!}

succ-leq-ℤ : (k : ℤ) → leq-ℤ k (succ-ℤ k)
succ-leq-ℤ k = {!!}

leq-ℤ-succ-leq-ℤ : (k l : ℤ) → leq-ℤ k l → leq-ℤ k (succ-ℤ l)
leq-ℤ-succ-leq-ℤ k l p = {!!}

le-ℤ : ℤ → ℤ → U
le-ℤ n m = {!!}

-- fam-shift-leq-ℤ : (k : ℤ) {i : Level} (P : (l : ℤ) → leq-ℤ k l → UU i) → (l : ℤ) → (leq-ℤ (succ-ℤ k) l) → UU i
-- fam-shift-leq-ℤ k P l p = {!!}

-- ind-Z-leqZ : (k : ℤ) {i : Level} (P : (l : ℤ) → (leqZ k l) → UU i) →
--   P k (reflexive-leqZ k) →
--   ((l : ℤ) (p : leqZ k l) → P l p → P (Zsucc l) (leqZ-succ-leqZ k l p)) →
--   (l : ℤ) (p : leqZ k l) → P l p
-- ind-Z-leqZ (inl Nzero) P pk pS (inl Nzero) star = pk
-- ind-Z-leqZ (inl Nzero) P pk pS (inl (Nsucc x)) ()
-- ind-Z-leqZ (inl Nzero) P pk pS (inr (inl star)) star = pS (inl Nzero) star pk
-- ind-Z-leqZ (inl Nzero) P pk pS (inr (inr Nzero)) star = pS (inr (inl star)) star (pS (inl Nzero) star pk)
-- ind-Z-leqZ (inl Nzero) P pk pS (inr (inr (Nsucc x))) star = pS (inr (inr x)) star (ind-Z-leqZ (inl Nzero) P pk pS (inr (inr x)) star)
-- ind-Z-leqZ (inl (Nsucc Nzero)) {i} P pk pS (inl Nzero) star = pS {!!} {!!} {!!}
-- ind-Z-leqZ (inl (Nsucc (Nsucc x))) {i} P pk pS (inl Nzero) star = {!!}
-- ind-Z-leqZ (inl (Nsucc x)) P pk pS (inl (Nsucc y)) p = {!!}
-- ind-Z-leqZ (inl (Nsucc x)) P pk pS (inr y) p = {!!}
-- ind-Z-leqZ (inr k) P pk pS l p = {!!}

-- Exercise 3.11
pred-ℤ : ℤ → ℤ
pred-ℤ n = {!!}

-- Exercise 3.12
add-ℤ : ℤ → ℤ → ℤ
add-ℤ n m = {!!}

neg-ℤ : ℤ → ℤ
neg-ℤ n = {!!}

\end{code}
