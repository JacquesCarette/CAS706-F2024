```agda
{-# OPTIONS --allow-unsolved-metas #-}
module CAS706.part2.Untyped where
```

Here: untyped intrinsically scope, call-by-name, full normalization
  (i.e. under lambda), non-deterministic reduction, reduction of
  open terms, tiny calculus.

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
```


## Untyped is Uni-typed

every term will have exactly the same type, written `★`
and pronounced "any".

## Syntax

```agda
infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_

infix  6  ƛ_
infix  6  ′_
infixl 7  _·_

data Type : Set where
  ★ : Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```
We let `Γ` and `Δ` range over contexts.

## Variables and the lookup judgment

```agda
data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A} → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A
```
Only insures that variables are in scope.

## Terms and the scoping judgment

Check that terms are well scoped but not that they are well typed:
```agda
data _⊢_ : Context → Type → Set where
  `_  : ∀ {Γ A} → Γ ∋ A          → Γ ⊢ A
  ƛ_  : ∀ {Γ}   → Γ , ★ ⊢ ★     → Γ ⊢ ★
  _·_ : ∀ {Γ}   → Γ ⊢ ★ → Γ ⊢ ★ → Γ ⊢ ★
```

## Writing variables as numerals

```agda
length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ ★
count {Γ , ★} {zero}    (s≤s z≤n)  =  Z
count {Γ , ★} {(suc n)} (s≤s p)    =  S (count p)

#_ : ∀ {Γ} → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
  → Γ ⊢ ★
#_ n {n∈Γ}  = ` count (toWitness n∈Γ)
```

## Test examples

```agda
twoᶜ : ∀ {Γ} → Γ ⊢ ★
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

fourᶜ : ∀ {Γ} → Γ ⊢ ★
fourᶜ = ƛ ƛ (# 1 · (# 1 · (# 1 · (# 1 · # 0))))

plusᶜ : ∀ {Γ} → Γ ⊢ ★
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

2+2ᶜ : ∅ ⊢ ★
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ
```

## Renaming

As before
```agda
ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
```

## Simultaneous substitution

Also exactly as before:
```agda
exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
```

## Single substitution

It is easy to define the special case of substitution for one free variable:
```agda
subst-zero : ∀ {Γ B} → (Γ ⊢ B) → ∀ {A} → (Γ , B ∋ A) → (Γ ⊢ A)
subst-zero M Z      =  M
subst-zero M (S x)  =  ` x

_[_] : ∀ {Γ A B} → Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} (subst-zero M) {A} N
```

## Neutral and normal terms

Reduction continues until a term is fully normalised.  Hence, instead
of values, we are now interested in _normal forms_.  Terms in normal
form are defined by mutual recursion with _neutral_ terms:
```agda
data Neutral : ∀ {Γ A} → Γ ⊢ A → Set
data Normal  : ∀ {Γ A} → Γ ⊢ A → Set
```
Neutral terms arise because we now consider reduction of open terms,
which may contain free variables.  A term is neutral if it is a
variable or a neutral term applied to a normal term:
```agda
data Neutral where
  `_  : ∀ {Γ A} (x : Γ ∋ A)                         → Neutral (` x)
  _·_  : ∀ {Γ} {L M : Γ ⊢ ★} → Neutral L → Normal M → Neutral (L · M)
```
A term is a normal form if it is neutral or an abstraction where the
body is a normal form. We use `′_` to label neutral terms.
Like `` `_ ``, it is unobtrusive:
```agda
data Normal where
  ′_ : ∀ {Γ A} {M : Γ ⊢ A}     → Neutral M    → Normal M
  ƛ_  : ∀ {Γ} {N : Γ , ★ ⊢ ★} → Normal N → Normal (ƛ N)
```

We introduce a convenient abbreviation for evidence that a variable is neutral:
```agda
#′_ : ∀ {Γ} (n : ℕ) {n∈Γ : True (suc n ≤? length Γ)} → Neutral {Γ} (# n)
#′_ n {n∈Γ}  =  ` count (toWitness n∈Γ)
```

For example, here is the evidence that the Church numeral two is in
normal form:
```agda
_ : Normal (twoᶜ {∅})
_ = ƛ ƛ (′ (#′ 1) · (′ ((#′ 1) · (′ (#′ 0)))))
```


## Reduction step

```agda
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ₁ : ∀ {Γ} {L L′ M : Γ ⊢ ★} → L —→ L′    → L · M —→ L′ · M
  ξ₂ : ∀ {Γ} {L M M′ : Γ ⊢ ★} → M —→ M′    → L · M —→ L · M′
  β : ∀ {Γ} {N : Γ , ★ ⊢ ★} {M : Γ ⊢ ★}   → (ƛ N) · M —→ N [ M ]
  ζ : ∀ {Γ} {N N′ : Γ , ★ ⊢ ★} → N —→ N′   → ƛ N —→ ƛ N′
```

## Reflexive and transitive closure

```agda
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where
  _∎ : (M : Γ ⊢ A) → M —↠ M
  step—→ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → M —↠ N → L —→ M → L —↠ N

pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

begin_ : ∀ {Γ A} {M N : Γ ⊢ A} → M —↠ N → M —↠ N
begin M—↠N = M—↠N
```

## Example reduction sequence

Here is the demonstration that two plus two is four
```agda
_ : 2+2ᶜ —↠ fourᶜ
_ =
  begin
    plusᶜ · twoᶜ · twoᶜ
  —→⟨ ξ₁ β ⟩
    (ƛ ƛ ƛ twoᶜ · # 1 · (# 2 · # 1 · # 0)) · twoᶜ
  —→⟨ β ⟩
    ƛ ƛ twoᶜ · # 1 · (twoᶜ · # 1 · # 0)
  —→⟨ ζ (ζ (ξ₁ β)) ⟩
    ƛ ƛ ((ƛ # 2 · (# 2 · # 0)) · (twoᶜ · # 1 · # 0))
  —→⟨ ζ (ζ β) ⟩
    ƛ ƛ # 1 · (# 1 · (twoᶜ · # 1 · # 0))
  —→⟨ ζ (ζ (ξ₂ (ξ₂ (ξ₁ β)))) ⟩
    ƛ ƛ # 1 · (# 1 · ((ƛ # 2 · (# 2 · # 0)) · # 0))
  —→⟨ ζ (ζ (ξ₂ (ξ₂ β))) ⟩
   ƛ (ƛ # 1 · (# 1 · (# 1 · (# 1 · # 0))))
  ∎
```


## Progress

Instead of claiming that every term either is a value
or takes a reduction step, we claim that every term
takes a reduction step or is in normal form.

Now we can demonstrate it for open, well-scoped terms.

```agda
data Progress {Γ A} (M : Γ ⊢ A) : Set where
  step : ∀ {N : Γ ⊢ A} → M —→ N   → Progress M
  done :                 Normal M → Progress M
```

If a term is well scoped then it satisfies progress:
```agda
progress : ∀ {Γ A} → (M : Γ ⊢ A) → Progress M
progress (` x) = done (′ (` x))
progress (ƛ trm) with progress trm
... | step x = step (ζ x)
... | done x = done (ƛ x)
progress (s · t) with progress s
... | step x = step (ξ₁ x)
... | done (ƛ x) = step β
... | done (′ x) with progress t
...    | step y = step (ξ₂ y)
...    | done y = done (′ x · y)
```

## Evaluation

```agda
record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ A} (N : Γ ⊢ A) : Set where
   done : Normal N → Finished N
   out-of-gas :      Finished N

data Steps : ∀ {Γ A} → Γ ⊢ A → Set where
  steps : ∀ {Γ A} {L N : Γ ⊢ A} → L —↠ N → Finished N → Steps L

eval : ∀ {Γ A} → Gas → (L : Γ ⊢ A) → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done NrmL                          =  steps (L ∎) (done NrmL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```
The definition is as before, save that the empty context `∅`
generalises to an arbitrary context `Γ`.

## Example

We reiterate our previous example. Two plus two is four, with Church numerals:
```agda
-- _ : eval (gas 100) 2+2ᶜ ≡ {!eval (gas 100) 2+2ᶜ!}
-- _ = refl
```

## Naturals and fixpoint

We could simulate naturals using Church numerals, but computing
predecessor is tricky and expensive.  Instead, we use a different
representation, called Scott numerals, where a number is essentially
defined by the expression that corresponds to its own case statement.

first three Church numerals as follows:

    zero  =  ƛ s ⇒ ƛ z ⇒ z
    one   =  ƛ s ⇒ ƛ z ⇒ s · z
    two   =  ƛ s ⇒ ƛ z ⇒ s · (s · z)

Scott numerals:

    zero = ƛ s ⇒ ƛ z ⇒ z
    one  = ƛ s ⇒ ƛ z ⇒ s · zero
    two  = ƛ s ⇒ ƛ z ⇒ s · one

Here is the Scott representation of naturals encoded with de Bruijn indexes:
```agda
`zero : ∀ {Γ} → (Γ ⊢ ★)
`zero = ƛ ƛ (# 0)

`suc_ : ∀ {Γ} → (Γ ⊢ ★) → (Γ ⊢ ★)
`suc_ M  = (ƛ ƛ ƛ (# 1 · # 2)) · M

case : ∀ {Γ} → (Γ ⊢ ★) → (Γ ⊢ ★) → (Γ , ★ ⊢ ★)  → (Γ ⊢ ★)
case L M N = L · (ƛ N) · M

-- let's see what one looks like
`one : ∀ {Γ} → (Γ ⊢ ★)
`one = ƛ ƛ (# 1) · `zero

-- let's see in Agda
`oneA : {A B B′ C : Set} → ((A → B → B) → C) → B′ → C
`oneA a b = a (λ a b → b)
```
Here we have been careful to retain the exact form of our previous
definitions.  The successor branch expects an additional variable to
be in scope (as indicated by its type), so it is converted to an
ordinary term using lambda abstraction.

```agda
_ : eval (gas 100) (`suc_ {∅} `zero) ≡
    steps
        ((ƛ (ƛ (ƛ # 1 · # 2))) · (ƛ (ƛ # 0))
    —→⟨ β ⟩
         ƛ (ƛ # 1 · (ƛ (ƛ # 0)))
    ∎)
    (done (ƛ (ƛ (′ (` (S Z)) · (ƛ (ƛ (′ (` Z))))))))
_ = refl
```

We can also define fixpoint.  Using named terms, we define:

    μ f = (ƛ x ⇒ f · (x · x)) · (ƛ x ⇒ f · (x · x))

This works because:

      μ f
    ≡
      (ƛ x ⇒ f · (x · x)) · (ƛ x ⇒ f · (x · x))
    —→
      f · ((ƛ x ⇒ f · (x · x)) · (ƛ x ⇒ f · (x · x)))
    ≡
      f · (μ f)

With de Bruijn indices, we have the following:
```agda
μ_ : ∀ {Γ} → (Γ , ★ ⊢ ★) → (Γ ⊢ ★)
μ N  =  (ƛ ((ƛ (# 1 · (# 0 · # 0))) · (ƛ (# 1 · (# 0 · # 0))))) · (ƛ N)
```

We can now define two plus two exactly as before:
```agda
infix 5 μ_

two : ∀ {Γ} → Γ ⊢ ★
two = `suc `suc `zero

four : ∀ {Γ} → Γ ⊢ ★
four = `suc `suc `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ ★
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))
```
Because `` `suc `` is now a defined term rather than primitive,
it is no longer the case that `plus · two · two` reduces to `four`,
but they do both reduce to the same normal term.


## Multi-step reduction is transitive

```agda
—↠-trans : ∀{Γ}{A}{L M N : Γ ⊢ A} → L —↠ M → M —↠ N → L —↠ N
—↠-trans (M ∎) mn = mn
—↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)
```

The following notation makes it convenient to employ
transitivity of `—↠`.

```agda
infixr 2 _—↠⟨_⟩_

_—↠⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A} → L —↠ M → M —↠ N → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = —↠-trans L—↠M M—↠N
```

## Multi-step reduction is a congruence

```agda
appL-cong : ∀ {Γ} {L L' M : Γ ⊢ ★} → L —↠ L' → L · M —↠ L' · M
appL-cong (_ ∎) = _ ∎
appL-cong (_ —→⟨ x ⟩ stps) = _ —→⟨ ξ₁ x ⟩ appL-cong stps






appR-cong : ∀ {Γ} {L M M' : Γ ⊢ ★} → M —↠ M' → L · M —↠ L · M'
appR-cong {Γ}{L}{M}{M'} (M ∎) = L · M ∎
appR-cong {Γ}{L}{M}{M'} (M —→⟨ r ⟩ rs) = L · M —→⟨ ξ₂ r ⟩ appR-cong rs

abs-cong : ∀ {Γ} {N N' : Γ , ★ ⊢ ★} → N —↠ N' → ƛ N —↠ ƛ N'
abs-cong (M ∎) = ƛ M ∎
abs-cong (L —→⟨ r ⟩ rs) = ƛ L —→⟨ ζ r ⟩ abs-cong rs
```

## Unicode

This chapter uses the following unicode:

    ★  U+2605  BLACK STAR (\st)

The `\st` command permits navigation among many different stars;
the one we use is number 7.
