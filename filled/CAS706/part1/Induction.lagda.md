```agda
module CAS706.part1.Induction where
```

## Imports

We require equality as in the previous chapter, plus the naturals
and some operations upon them.  We also require a couple of new operations,
`cong`, `sym`, `_≡⟨⟩_` and `_≡⟨_⟩_`, which are explained below:
```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; step-≡-⟨; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
```
(Importing `step--∣` defines `_≡⟨⟩_` and importing `step-≡-⟩` defines `_≡⟨_⟩_`.)


## Properties of operators

* _Identity_.
* _Associativity_.
* _Commutativity_. 
* _Distributivity_. 

## Associativity

```agda
_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎
```

## Let us start proving

(CAS706: these are done in a different order than in PLFA. The
reason is that the interactive version illustrate slightly different
ideas than the "paper" version.)

```agda
+-identityˡ : ∀ (m : ℕ) → zero + m ≡ m
+-identityˡ m = refl

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)
```

```agda
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-identityʳ n)
+-comm (suc m) n = begin
  suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
  suc (n + m) ≡⟨ sym (+-suc n m) ⟩
  n + suc m   ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)
```


## Our first corollary: rearranging {#sections}
-- no cases! But: left assoc of +, sym, eq. sym, sections.
```agda
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q = begin
  (m + n) + (p + q)  ≡⟨ +-assoc (m + n) p q ⟨
  ((m + n) + p) + q  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩ 
  m + (n + p) + q    ∎
```

## Associativity with rewrite

```agda
+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl
```

## Commutativity with rewrite

```agda
+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl
```


## Standard library

```agda
import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
```

## Unicode

This chapter uses the following unicode:

    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).
