```agda
module CAS706.part1.Negation where
```

## Imports

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_)
open import Relation.Nullary.Negation using (contradiction)
open import CAS706.part1.Isomorphism using (_≃_; extensionality)
```

## Negation

```agda
¬_ : Set → Set
¬ A = A → ⊥
```
If both `¬ A` and `A` hold, then we have a contradiction:
```agda
¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬a a = ¬a a

infix 3 ¬_
```
In _classical_ logic, we have that `A` is equivalent to `¬ ¬ A`.
In _intuitionistic_ logic, where
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`:
```agda
¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro a ¬a = ¬a a
```
(do it all on the right, and also half-and-half)

We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`:
```agda
¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬a  a = ¬¬¬a (¬¬-intro a)

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬b a = ¬b (f a)
```

```agda
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()
```

Two ways of writing a function on this type
```agda
id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()
```
But, using extensionality, we can prove these equal:
```agda
id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())
```
Without extensionality, they are not, but this is not provable inside Agda.

```agda
assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = refl
```

## Intuitive and Classical logic

Intuinistic ~~ logic of _evidence_.
Classical   ~~ logic of _truth_.

## Excluded middle is irrefutable

```agda
postulate
  em : ∀ {A : Set} → A ⊎ ¬ A
```
EM does not hold in
intuitionistic logic.  However, we can show that it is _irrefutable_,
meaning that the negation of its negation is provable (and hence that
its negation is never provable):
```agda
em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable x = x (inj₂ (λ a → x (inj₁ a)))
```
## Standard Prelude

```agda
import Relation.Nullary.Negation using (¬_; contradiction; contraposition)
```

## Unicode

This chapter uses the following unicode:

    ¬  U+00AC  NOT SIGN (\neg)
    ≢  U+2262  NOT IDENTICAL TO (\==n)
