```agda
{-# OPTIONS --allow-unsolved-metas --exact-split #-}
module CAS706.part1.Isomorphism where
```

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; trans)
open Eq.≡-Reasoning
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Function.Base using (id)
```

## "variables"
JC: not in PLFA, but some of this is tedious, so now's a good time

```agda
private
  variable
    A B C : Set
```

## Function composition

```agda
infixr 5 _∘_
_∘_ : (B → C) → (A → B) → A → C
(g ∘ f) x  = g (f x)

_∘′_ : (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)
```

## Extensionality {#extensionality}

```agda
postulate
  extensionality : {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

Split on n instead:
```agda
_+′_ : ℕ → ℕ → ℕ
m +′ zero = m
m +′ suc n = suc (m +′ n)
```

```agda
same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n = begin
  m +′ n ≡⟨ helper m n ⟩
  n + m  ≡⟨ +-comm n m ⟩
  m + n  ∎
  where
    helper : (a b : ℕ) → a +′ b ≡ b + a
    helper a zero = refl
    helper a (suc b) = cong suc (helper a b)
```
But what about:
```agda
same : _+′_ ≡ _+_
same = extensionality λ x → extensionality λ y → same-app x y
```

```agda
postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

## Isomorphism

```agda
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  constructor mk-≃ -- not in PLFA
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_
```

Almost the same as, but records are *way* more convenient:
```agda
data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g
```

## Isomorphism is an equivalence

```agda
≃-refl : A ≃ A
≃-refl = mk-≃ id id (λ _ → refl) λ _ → refl
```
(show as record and with constructor and with copatterns)

```agda
≃-sym : A ≃ B → B ≃ A
≃-sym A≃B = mk-≃ (from A≃B) (to A≃B) (to∘from A≃B) (from∘to A≃B)

≃-sym′ : A ≃ B → B ≃ A
≃-sym′ (mk-≃ a b c d) = mk-≃ b a d c -- horrible names!

≃-sym″ : A ≃ B → B ≃ A
≃-sym″ x .to = x .from
≃-sym″ x .from = x .to
≃-sym″ x .from∘to = x .to∘from
≃-sym″ x .to∘from = x .from∘to
```

To show isomorphism is transitive, we compose the `to` and `from`
functions, and use equational reasoning to combine the inverses:
```agda
≃-trans : A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C .to = to B≃C ∘ to A≃B -- λ x → to B≃C (to A≃B x)
≃-trans A≃B B≃C .from = from A≃B ∘ from B≃C
≃-trans A≃B B≃C .from∘to = λ x → begin
  from A≃B (from B≃C (to B≃C (to A≃B x))) ≡⟨ cong (from A≃B) (from∘to B≃C _) ⟩
  from A≃B (to A≃B x)                     ≡⟨ from∘to A≃B _ ⟩
  x                                       ∎
≃-trans A≃B B≃C .to∘from = λ y → trans (cong (to B≃C) (to∘from A≃B _)) (to∘from B≃C y)
-- recall: the "proof development" in the `trans` style was *way* more painful!
```

## Equational reasoning for isomorphism

```agda
module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : A ≃ B → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : (A : Set) → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) → A ≃ A
  _ ≃-∎ = ≃-refl

open ≃-Reasoning
```

## Embedding

```agda
infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl .to = id
≲-refl .from = id
≲-refl .from∘to = λ _ → refl

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C .to = to B≲C ∘ to A≲B
≲-trans A≲B B≲C .from = from A≲B ∘ from B≲C
≲-trans A≲B B≲C .from∘to x = begin
  (from A≲B ∘ from B≲C ∘ to B≲C ∘ to A≲B) x ≡⟨ cong (from A≲B) (from∘to B≲C _) ⟩
  (from A≲B ∘ to A≲B) x                     ≡⟨ from∘to A≲B x ⟩
  x ∎
```

It is also easy to see that if two types embed in each other, and the
embedding functions correspond, then they are isomorphic.  This is a
weak form of anti-symmetry:
```agda
≲-antisym :(A≲B : A ≲ B) → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A) → (from A≲B ≡ to B≲A)
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to .to = to A≲B
≲-antisym A≲B B≲A to≡from from≡to .from = from A≲B
≲-antisym A≲B B≲A to≡from from≡to .from∘to x = from∘to A≲B x
  
≲-antisym A≲B B≲A to≡from from≡to .to∘from y = begin
  to A≲B (from A≲B y)   ≡⟨ cong-app to≡from _ ⟩
  from B≲A (from A≲B y) ≡⟨ cong (from B≲A) (cong-app from≡to _) ⟩
  from B≲A (to B≲A y)   ≡⟨ B≲A .from∘to y ⟩
  y                     ∎
```

## Equational reasoning for embedding

```agda
module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : A ≲ B  → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) → A ≲ B → B ≲ C → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set) → A ≲ A
  _ ≲-∎ = ≲-refl

open ≲-Reasoning
```

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
```agda
import Function.Base using (_∘_)
import Function.Bundles using (_↔_; _↩_)
```
The standard library `_↔_` and `_↩_` correspond to our `_≃_` and
`_≲_`, respectively, but those in the standard library are less
more general (i.e. less convenient).

## Unicode

    ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
    ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
    ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
