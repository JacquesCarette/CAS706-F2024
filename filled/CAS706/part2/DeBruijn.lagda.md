```agda
{-# OPTIONS --allow-unsolved-metas #-}
module CAS706.part2.DeBruijn where
```

Names -> de Bruijn indices
terms indexed by types
is much nicer

Untyped terms + typing rules (Curry style, extrinsic)
typed terms (Church style, intrinsic)

The particular representation described here
was first proposed by
Thorsten Altenkirch and Bernhard Reus.
The formalisation of renaming and substitution
we use is due to Conor McBride.
Related work has been carried out by
James Chapman, James McKinna, and many others.

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
```

## Introduction

recall: term and typing derivations had very similar structure

    plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
    plus = μ ƛ ƛ case (# 1) (# 0) (`suc (# 3 · # 0 · # 1))

Presentation of the material is now forcibly more 'entertwined',
but overall shorter.

## Syntax

```agda
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_
```

Since terms are intrinsically typed, we must define types and
contexts before terms.

```agda
data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```
Example
```agda
_ : Context
_ = ∅ , `ℕ ⇒ `ℕ , `ℕ
```

### Variables and the lookup judgment

Intrinsically-typed variables correspond to the lookup judgment.
```agda
data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A} → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A
```

### Terms and the typing judgment

```agda
data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
  ƛ_  : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_ : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  `zero : ∀ {Γ} → Γ ⊢ `ℕ
  `suc_ : ∀ {Γ} → Γ ⊢ `ℕ → Γ ⊢ `ℕ
  case : ∀ {Γ A} → Γ ⊢ `ℕ → Γ ⊢ A → Γ , `ℕ ⊢ A → Γ ⊢ A
  μ_ : ∀ {Γ A} → Γ , A ⊢ A → Γ ⊢ A
```

use the derivation _as_ the term

### Abbreviating de Bruijn indices

```agda
length : Context → ℕ
length ∅ = 0
length (c , x) = suc (length c)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p
```

Can go in the opposite direction:
```agda
count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {Γ , x} {zero} (s≤s z≤n) = Z
count {Γ , x} {suc n} (s≤s p) = S (count p)
```

JC: I think using `Fin` would make things even nicer.

Convenient abbreviation for variables:
```agda
#_ : ∀ {Γ} → (n : ℕ) → {n∈Γ : True (suc n ≤? length Γ)}
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ _ {n∈Γ}  =  ` count (toWitness n∈Γ)
```

With this abbreviation, we can rewrite the Church numeral two more compactly:
```agda
_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ (# 1 · (# 1 · # 0)) -- this is for the Borg... but we'll do this one
```

### Test examples
We repeat the test examples from Chapter [Lambda](/Lambda/).
```agda
two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∀ {Γ} → Γ ⊢ `ℕ
2+2 = plus · two · two
```
We generalise to arbitrary contexts because later we will give examples
where `two` appears nested inside binders.

```agda
Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

plusᶜ : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

sucᶜ : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc (# 0)

2+2ᶜ : ∀ {Γ} → Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
```

## Renaming

```agda
ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z = Z
ext ρ (S i) = S ρ i
```
Now we can remame (as a function, instead of a theorem), using
ext when we encounter binders:
```agda
rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x) = ` ρ x
rename ρ (ƛ trm) = ƛ rename (ext ρ) trm
rename ρ (trm · trm₁) = rename ρ trm · rename ρ trm₁
rename ρ `zero = `zero
rename ρ (`suc trm) = `suc rename ρ trm
rename ρ (case trm trm₁ trm₂) =
  case (rename ρ trm) (rename ρ trm₁) (rename (ext ρ) trm₂)
rename ρ (μ trm) = μ (rename (ext ρ) trm)
```

Here is an example of renaming a term with one free
and one bound variable:
```agda
M₀ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₀ = ƛ (# 1 · (# 1 · # 0))

M₁ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
M₁ = ƛ (# 2 · (# 2 · # 0))

_ : rename S_ M₀ ≡ M₁
_ = refl
```
In general, `rename S_` will increment the de Bruijn index for
each free variable by one, while leaving the index for each
bound variable unchanged.  The code achieves this naturally:
the map originally increments each variable by one, and is
extended for each bound variable by a map that leaves it
unchanged.

We will see below that renaming by `S_` plays a key role in
substitution.  For traditional uses of de Bruijn indices
without intrinsic typing, this is a little tricky. The code
keeps count of a number where all greater indexes are free and
all smaller indexes bound, and increment only indexes greater
than the number. It's easy to have off-by-one errors.  But
it's hard to imagine an off-by-one error that preserves
typing, and hence the Agda code for intrinsically-typed de Bruijn
terms is intrinsically reliable.


## Simultaneous Substitution

- arbitrary arity (i.e. all free variables at once)
- subst. terms in arbitrary context (i.e. not closed)

Given a map from variables in one context to terms over
another, extension yields a map from the first context
extended to the second context similarly extended:
```agda
exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z = ` Z
exts σ (S pos) = rename S_ (σ pos)
```

This subst now looks like the old rename!
```agda
subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` x)          =  σ x
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
subst σ (`suc M)       =  `suc (subst σ M)
subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N)          =  μ (subst (exts σ) N)
```

## Single substitution

From the general case of substitution for multiple free
variables it is easy to define the special case of
substitution for one free variable:
```agda
_[_] : ∀ {Γ A B}  → Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst σ N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z = M
  σ (S pos) = ` pos
```

```agda
M₂ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₂ = ƛ # 1 · (# 1 · # 0)

M₃ : ∅ ⊢ `ℕ ⇒ `ℕ
M₃ = ƛ `suc # 0

M₄ : ∅ ⊢ `ℕ ⇒ `ℕ
M₄ = ƛ (ƛ `suc # 0) · ((ƛ `suc # 0) · # 0)

_ : M₂ [ M₃ ] ≡ M₄
_ = refl
```

This needs 'renaming' to avoid capture:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] `` should yield
  `` ƛ "z" ⇒ ` "z" · (` "x" · `zero) ``

Say the bound `"x"` has type `` `ℕ ⇒ `ℕ ``, the substituted
`"y"` has type `` `ℕ ``, and the free `"x"` also has type `` `ℕ ⇒ `ℕ ``.
```agda
M₅ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₅ = ƛ # 0 · # 1

M₆ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ
M₆ = # 0 · `zero

M₇ : ∅ , `ℕ ⇒ `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₇ = ƛ (# 0 · (# 1 · `zero))

_ : M₅ [ M₆ ] ≡ M₇
_ = refl
```

### Values

The definition of value is much as before:
```agda
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ :    ∀ {Γ A B} {N : Γ , A ⊢ B}          → Value (ƛ N)
  V-zero : ∀ {Γ}                              → Value (`zero {Γ})
  V-suc :  ∀ {Γ} {V : Γ ⊢ `ℕ}       → Value V → Value (`suc V)
```

## Reduction

Reduction is very similar, but typed.
```agda
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ----------------
    → μ N —→ N [ μ N ]
```

## Reflexive and transitive closure

```agda
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A) → M —↠ M
  step—→ : (L : Γ ⊢ A) {M N : Γ ⊢ A} → M —↠ N → L —→ M
    → L —↠ N

pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

begin_ : ∀ {Γ A} {M N : Γ ⊢ A} → M —↠ N → M —↠ N
begin M—↠N = M—↠N
```


## Examples

```agda
_ : twoᶜ · sucᶜ · `zero {∅} —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ (sucᶜ · (sucᶜ · # 0))) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
   `suc (`suc `zero)
  ∎
```

Next, a sample reduction demonstrating that two plus two is four:
(skipped, too long)

## Progress

```agda
data Progress {A} (M : ∅ ⊢ A) : Set where
  step : ∀ {N : ∅ ⊢ A} → M —→ N → Progress M
  done : Value M → Progress M
```

The statement and proof of progress is much as before:
```agda
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ N)                          =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                     =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                 =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                    =  step (β-ƛ VM)
progress (`zero)                        =  done V-zero
progress (`suc M) with progress M
...    | step M—→M′                     =  step (ξ-suc M—→M′)
...    | done VM                        =  done (V-suc VM)
progress (case L M N) with progress L
...    | step L—→L′                     =  step (ξ-case L—→L′)
...    | done V-zero                    =  step (β-zero)
...    | done (V-suc VL)                =  step (β-suc VL)
progress (μ N)                          =  step (β-μ)
```

## Evaluation

```agda
record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ A} (N : Γ ⊢ A) : Set where
   done : Value N → Finished N
   out-of-gas :     Finished N

-- multi-step arrow
data Steps {A} : ∅ ⊢ A → Set where
  steps : {L N : ∅ ⊢ A} → L —↠ N → Finished N → Steps L

eval : ∀ {A} → Gas → (L : ∅ ⊢ A) → Steps L
eval (gas zero) tm = steps (tm ∎) out-of-gas
eval (gas (suc amount)) tm with progress tm
... | done Vtm = steps (tm ∎) (done Vtm)
... | step {N} st with eval (gas amount) N
...     | steps sts fin = steps (step—→ tm sts st) fin
```

## Examples

We reiterate each of our previous examples.  We re-define the term
`sucμ` that loops forever:
```agda
sucμ : ∅ ⊢ `ℕ
sucμ = μ (`suc (# 0))
```
To compute the first three steps of the infinite reduction sequence,
we evaluate with three steps worth of gas:
```agda
_ : eval (gas 3) sucμ ≡
  steps
   (μ `suc ` Z
   —→⟨ β-μ ⟩
    `suc (μ `suc ` Z)
   —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ `suc ` Z))
   —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ `suc ` Z)))
   ∎)
   out-of-gas
_ = refl
```

The Church numeral two applied to successor and zero:

_ : eval (gas 100) (twoᶜ · sucᶜ · `zero) ≡
  {!eval (gas 100) (twoᶜ · sucᶜ · `zero)!}
_ = {!!}


Two plus two is four:

_ : eval (gas 100) (plus · two · two) ≡
     {!eval (gas 100) (plus · two · two)!}
_ = {!!}


And the corresponding term for Church numerals:

_ : eval (gas 100) (plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero) ≡
    {!!}
_ = {!!}


We omit the proof that reduction is deterministic, since it is
tedious and almost identical to the previous proof.


## Intrinsic typing is golden

Counting the lines of code is instructive.  While this chapter
covers the same formal development as the previous two
chapters, it has much less code.  Omitting all the examples,
and all proofs that appear in Properties but not DeBruijn
(such as the proof that reduction is deterministic), the
number of lines of code is as follows:

    Lambda                      216
    Properties                  235
    DeBruijn                    276

The relation between the two approaches approximates the
golden ratio: extrinsically-typed terms
require about 1.6 times as much code as intrinsically-typed.

## Unicode

This chapter uses the following unicode:

    σ  U+03C3  GREEK SMALL LETTER SIGMA (\Gs or \sigma)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₃  U+20B3  SUBSCRIPT THREE (\_3)
    ₄  U+2084  SUBSCRIPT FOUR (\_4)
    ₅  U+2085  SUBSCRIPT FIVE (\_5)
    ₆  U+2086  SUBSCRIPT SIX (\_6)
    ₇  U+2087  SUBSCRIPT SEVEN (\_7)
    ≠  U+2260  NOT EQUAL TO (\=n)
