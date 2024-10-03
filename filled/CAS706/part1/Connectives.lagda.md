```agda
module CAS706.part1.Connectives where
```

_Propositions as Types_:

  * _conjunction_ is _product_,
  * _disjunction_ is _sum_,
  * _true_ is _unit type_,
  * _false_ is _empty type_,
  * _implication_ is _function space_.


## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat.Base using (ℕ)
open import Function.Base using (_∘_)

open import CAS706.part1.Isomorphism using (_≃_; mk-≃; _≲_; extensionality)
open _≃_
open CAS706.part1.Isomorphism.≃-Reasoning
```

## Conjunction is product

```agda
data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x
proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_
```

Alternatively (and actually much better):
```agda
record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_
```
Because, in part:
```agda
η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ _ = refl
```
Q: how to prove the equality of two records?
```agda
record Foo : Set where
  field
    AA : ℕ
    BB : ℕ

open Foo

-- Answer: you prove that all of the fields are the same, i.e. pointwise
Foo≡ : {a b : Foo} → AA a ≡ AA b → BB a ≡ BB b → a ≡ b
Foo≡ refl refl = refl
```

```agda
data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
```

A "proof" that `Bool × Tri` has 6 members:
```agda
×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6
```

```agda
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm = mk-≃
  (λ { ⟨ a , b ⟩ → ⟨ b , a ⟩})
  (λ { ⟨ b , a ⟩ → ⟨ a , b ⟩ })
  (λ { ⟨ a , b ⟩ → refl})
  (λ { ⟨ _ , _ ⟩ → refl})

×-comm′ : ∀ {A B : Set} → A ×′ B ≃ B ×′ A
×-comm′ = mk-≃
  (λ { ⟨ a , b ⟩′ → ⟨ b , a ⟩′})
  (λ { ⟨ b , a ⟩′ → ⟨ a , b ⟩′})
  (λ { ⟨ a , b ⟩′ → refl})
  (λ { ⟨ _ , _ ⟩′ → refl})

swap : {A B : Set} → A ×′ B → B ×′ A
swap p = ⟨ proj₂′ p , proj₁′ p ⟩′ 

swap∘swap : {A B : Set} (x : A ×′ B) → swap (swap x) ≡ x
swap∘swap = η-×′

×-comm″ : ∀ {A B : Set} → A ×′ B ≃ B ×′ A
×-comm″ = mk-≃
  swap
  swap
  swap∘swap
  η-×′
```

```agda
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = mk-≃ assocʳ assocˡ assocˡʳ assocʳˡ
  where
    assocʳ : {X Y Z : Set} → (X × Y) × Z → X × (Y × Z)
    assocʳ ⟨ ⟨ x , y ⟩ , z ⟩ = ⟨ x , ⟨ y , z ⟩ ⟩
    
    assocˡ : {X Y Z : Set} → X × (Y × Z) → (X × Y) × Z
    assocˡ ⟨ x , ⟨ y , z ⟩ ⟩ = ⟨ ⟨ x , y ⟩ , z ⟩
    
    assocˡʳ : {X Y Z : Set} → (x : (X × Y) × Z) → assocˡ (assocʳ x) ≡ x
    assocˡʳ ⟨ ⟨ x , y ⟩ , z ⟩ = refl
    
    assocʳˡ : {X Y Z : Set} → (x : X × (Y × Z)) → assocʳ (assocˡ x) ≡ x
    assocʳˡ ⟨ x , ⟨ y , z ⟩ ⟩ = refl

```

## Truth is unit

```agda
data ⊤ : Set where  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl
```

Alternatively:
```agda
record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl -- not obvious

truth′ : ⊤′
truth′ = _
```

```agda
⊤-count : ⊤ → ℕ
⊤-count tt = 1
```

```agda
⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ .to     ⟨ _ , a ⟩ = a
⊤-identityˡ .from   a        = ⟨ tt , a ⟩
⊤-identityˡ .from∘to ⟨ tt , a ⟩  = refl
⊤-identityˡ .to∘from a          = refl
```

```agda
⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} = ≃-begin
  (A × ⊤) ≃⟨ ×-comm ⟩
  (⊤ × A) ≃⟨ ⊤-identityˡ ⟩
  A ≃-∎ -- can do it equationally!
```

## Disjunction is sum

```agda
data _⊎_ (A B : Set) : Set where

  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
```
evidence

Eliminator
```agda
case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ x) = g x
```

```agda
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ x) = refl
```
More generally, we can also throw in an arbitrary function from a disjunction:
```agda
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ x) = refl

infixr 1 _⊎_
```

More counting
```agda
⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5
```


## False is empty

```agda
data ⊥ : Set where
  -- no clauses!
```
There is no possible evidence that `⊥` holds.

Dual to `⊤`, for `⊥` there is no introduction rule but an elimination rule.
```agda
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()
```

```agda
⊥-count : ⊥ → ℕ
⊥-count ()
```
## Implication is function {#implication}

```agda
→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim L M = L M
```
Used to be known as _modus ponens_.

λ is introduction, application is elimination.

Elimination followed by introduction is the identity:
```agda
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl
```

```agda
→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9
```

Corresponding to the law

    (p ^ n) ^ m  ≡  p ^ (n * m)

we have the isomorphism

    A → (B → C)  ≃  (A × B) → C

```agda
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying .to        f ⟨ a , b ⟩ = f a b
currying .from      g   a   b  = g ⟨ a , b ⟩
currying .from∘to   f = η-→ f
currying .to∘from   g = extensionality λ { ⟨ a , b ⟩ → refl}
```

Corresponding to the law

    p ^ (n + m) = (p ^ n) * (p ^ m)

we have the isomorphism:

    (A ⊎ B) → C  ≃  (A → C) × (B → C)

```agda
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ .to h = ⟨ h ∘ inj₁ , h ∘ inj₂ ⟩
→-distrib-⊎ .from ⟨ f , g ⟩ = case-⊎ f g
→-distrib-⊎ .from∘to h = extensionality (uniq-⊎ h)
→-distrib-⊎ .to∘from ⟨ f , g ⟩ = refl
```

Corresponding to the law

    (p * n) ^ m = (p ^ m) * (n ^ m)

we have the isomorphism:

    A → B × C  ≃  (A → B) × (A → C)

```agda
→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× = {!!}
```

## Distribution

```agda
×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = {!!}
```

Sums do not distribute over products up to isomorphism, but it is an embedding:
```agda
⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× ._≲_.to (inj₁ ⟨ a , b ⟩ ) = ⟨ inj₁ a , inj₁ b ⟩
⊎-distrib-× ._≲_.to (inj₂ x) = ⟨ inj₂ x , inj₂ x ⟩
⊎-distrib-× ._≲_.from ⟨ inj₁ x , inj₁ y ⟩ = inj₁ ⟨ x , y ⟩
⊎-distrib-× ._≲_.from ⟨ inj₁ x , inj₂ y ⟩ = inj₂ y
⊎-distrib-× ._≲_.from ⟨ inj₂ x , x₁ ⟩ = inj₂ x
⊎-distrib-× ._≲_.from∘to (inj₁ ⟨ x , x₁ ⟩) = refl
⊎-distrib-× ._≲_.from∘to (inj₂ x) = refl
```

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
```agda
import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Data.Unit using (⊤; tt)
import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Data.Empty using (⊥; ⊥-elim)
import Function.Bundles using (_⇔_)
```
## Unicode

This chapter uses the following unicode:

    ×  U+00D7  MULTIPLICATION SIGN (\x)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
