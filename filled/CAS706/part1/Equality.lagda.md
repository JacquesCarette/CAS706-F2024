```agda
module CAS706.part1.Equality where
```

## Imports -- none!

## Equality

```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_
```

## Equality is an equivalence relation

```agda
sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
```

## Congruence and substitution {#cong}

```agda
cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x → v ≡ y → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

cong-app′ : ∀ {A B : Set} {f g : A → B} → f ≡ g
  → ∀ {x : A} → f x ≡ g x
cong-app′ refl = refl
```

```agda
subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y → P x → P y
subst P refl px = px
```

## Chains of equations (simplified)

```agda
module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ step-≡
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ x y≡z x≡y = trans x≡y y≡z

  syntax step-≡ x y≡z x≡y  =  x ≡⟨  x≡y ⟩ y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl

open ≡-Reasoning
```

-- why not directly?
```agda
_≡⟨_⟩′_ : ∀ {A : Set} (x : A) {y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
x ≡⟨ x≡y ⟩′ y≡z  =  trans x≡y y≡z
```
Showing the use, PLFA style
```agda
trans′ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans′ {_} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎
```

My preferred style
```agda
trans″ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans″ {_} {x} {y} {z} x≡y y≡z = begin
  x  ≡⟨ x≡y ⟩
  y  ≡⟨ y≡z ⟩
  z  ∎
```

## Chains of equations, another example

```agda
-- we have to repeat this because of stuff we'll do below
-- that would otherwise conflict
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = begin
    m + zero  ≡⟨ +-identity m ⟩
    m         ≡⟨⟩
    zero + m  ∎
+-comm m (suc n) =  begin
    m + suc n    ≡⟨ +-suc m n ⟩
    suc (m + n)  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)  ≡⟨⟩
    suc n + m    ∎
```

## Rewriting

```agda
data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm m n ev rewrite +-comm n m = ev
```

## Multiple rewrites

```agda
+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero    n  rewrite +-identity n             =  refl
+-comm′ (suc m) n  rewrite +-suc n m | +-comm′ m n  =  refl
```
Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible. JC: Furthermore proofs with rewrite tend to be quite
fragile, i.e. unstable under refactoring, while ones with chains
of equalities are much easier to repair.


## Rewriting expanded

```agda
even-comm′ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl       = ev

-- of course here it's not even needed
even-comm″ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm″ m n ev =  subst even (+-comm m n) ev
```

## Leibniz equality

We used Martin-Löf (1975).
Earlier: Leibniz, 1686.

Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties.

```agda
_≐_ : ∀ {A : Set} → A → A → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y
```

```agda
refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ P Px  =  Px

trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ x≐y y≐z P Px  = y≐z P (x≐y P Px) -- (x≐y P Px)

-- This one is quite tricky!
sym-≐ : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P = x≐y Q (λ t → t)
  where
    Q : A → Set
    Q = λ z → P z → P x

≡-implies-≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ refl P = λ t → t

-- need to invent a property again
≐-implies-≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y  = x≐y Q refl
  where
    Q : A → Set
    Q z = x ≡ z
```

JC: if this interests you, I can give you more to read.

## Universe polymorphism {#unipoly}

```agda
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡′ y → y ≡′ x
sym′ refl′ = refl′

_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)
```

[docs]: https://agda.readthedocs.io/en/v2.6.1/language/universe-levels.html


## Standard library

```agda
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
```

## Unicode

This chapter uses the following unicode:

    ≡  U+2261  IDENTICAL TO (\==, \equiv)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
    ⊔  U+2294  SQUARE CUP (\lub)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
