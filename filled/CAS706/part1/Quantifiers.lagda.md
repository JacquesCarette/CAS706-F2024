```agda
module CAS706.part1.Quantifiers where
```

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary.Negation using (¬_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import CAS706.part1.Isomorphism
  using (_≃_; ≃-sym; extensionality; ∀-extensionality)
open import Function.Base using (_∘_)

open _≃_
```

## Universals

```agda
∀-elim : ∀ {A : Set} {B : A → Set} → (L : ∀ (x : A) → B x) → (M : A)
  → B M

∀-elim L M = L M
```

## Existentials

```agda
record Σ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    proj₁ : A
    proj₂ : B proj₁
```
A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
```agda
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set} → (∀ x → B x → C) → ∃[ x ] B x
  → C
-- ∃-elim f ⟨ a , b ⟩ = f a b
∃-elim f = λ x → f (Σ.proj₁ x) (Σ.proj₂ x)
```

Before we launch into currying, it's good to show we have η for Σ as well:
```agda
η-Σ : {A : Set} {B : A → Set} → (x : Σ A B) → ⟨ Σ.proj₁ x , Σ.proj₂ x ⟩ ≡ x
η-Σ _ = refl
```

and now back to our regular schedule:
```agda
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying .to = ∃-elim
∀∃-currying .from f a b = f ⟨ a , b ⟩
∀∃-currying .from∘to f = refl
∀∃-currying .to∘from f = refl -- but really uses η-→ and η-Σ
```

## An existential example

Recall the definitions of `even` and `odd` from
Chapter [Relations](/Relations/):
```agda
open import CAS706.part1.Relations using (even; odd; zero; suc)
```

Equvalence of two obvious ways of defining even/odd:
```agda
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ zero = ⟨ 0 , refl ⟩
even-∃ (suc on) with odd-∃ on
... | ⟨ m , m-odd ⟩ = ⟨ suc m , Eq.cong suc m-odd ⟩

odd-∃ (suc en) with ⟨ m , m-evn ⟩ ← even-∃ en = ⟨ m , Eq.cong suc m-evn ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even m-evn = {!!}

∃-odd m-odd = {!!}
```

## Existentials, Universals, and Negation

```agda
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set} → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ = ≃-sym ∀∃-currying
{-
¬∃≃∀¬ .to = ∀∃-currying .from -- f a b = f ⟨ a , b ⟩
¬∃≃∀¬ .from = ∀∃-currying .to
¬∃≃∀¬ .from∘to = {!!}
¬∃≃∀¬ .to∘from = {!!}
-}
```

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
```agda
import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
```

## Unicode

This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)
