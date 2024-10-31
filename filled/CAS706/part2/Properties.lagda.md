```agda
{-# OPTIONS --allow-unsolved-metas #-}
module CAS706.part2.Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Function.Base using (_∘_)

-- open import plfa.part1.Isomorphism
open import CAS706.part2.Lambda
```

We might expect is that every term is either a value or can take
a reduction step.  As we will see, this property does _not_ hold for
every term, but it does hold for every closed, well-typed term.

_Progress_: If `∅ ⊢ M ⦂ A` then either `M` is a value or there is an `N` such
that `M —→ N`.

_Preservation_: If `∅ ⊢ M ⦂ A` and `M —→ N` then `∅ ⊢ N ⦂ A`.

## Values do not reduce

```agda
V¬—→ : ∀ {M N} → Value M → ¬ (M —→ N)
V¬—→ (V-suc v) (ξ-suc r) = V¬—→ v r
```
As a corollary, terms that reduce are not values:
```agda
—→¬V : ∀ {M N} → M —→ N → ¬ Value M
-- —→¬V (ξ-suc M—→N) (V-suc VM) = —→¬V M—→N VM  -- direct proof

—→¬V M—→N VM = V¬—→ VM M—→N -- corollary proof
```


If we expand out the negations, we have

    V¬—→ : ∀ {M N} → Value M → M —→ N → ⊥
    —→¬V : ∀ {M N} → M —→ N → Value M → ⊥

which are the same function with the arguments swapped.


## Progress
_Progress_: If `∅ ⊢ M ⦂ A` then either `M` is a value or there is an `N` such
that `M —→ N`.

However, this is not true in general.  Ex 1:

    `zero · `suc `zero

Ex 2: if `` "s" ⦂ `ℕ ⇒ `ℕ ``

     ` "s" · `zero


```agda
data Progress (M : Term) : Set where
  step : ∀ {N} → M —→ N → Progress M
  done : Value M → Progress M
```

If a term is well typed in the empty context then it satisfies progress:
```agda
progress : ∀ {M A} → ∅ ⊢ M ⦂ A → Progress M
progress (⊢ƛ typ) = done V-ƛ
progress (typ · typ₁) with progress typ
... | step x = step ( ξ-·₁ x)
... | done V-ƛ with progress typ₁
... | step x = step (ξ-·₂ V-ƛ x)
... | done x = step (β-ƛ x)
progress ⊢zero = done V-zero
progress (⊢suc typ) with progress typ
... | step x = step (ξ-suc x)
... | done x = done (V-suc x)
progress (⊢case typ typ₁ typ₂) with progress typ
... | step x = step (ξ-case x)
... | done V-zero = step β-zero
... | done (V-suc x) = step (β-suc x)
progress (⊢μ typ) = step β-μ

```
Our code reads neatly in part because we consider the
`step` option before the `done` option. We could, of course,
do it the other way around, but then the `...` abbreviation
no longer works, and we will need to write out all the arguments
in full. In general, the rule of thumb is to consider the easy case
(here `step`) before the hard case (here `done`).
If you have two hard cases, you will have to expand out `...`
or introduce subsidiary functions.

Instead of defining a data type for `Progress M`, we could
have formulated progress using disjunction and existentials:
```agda
postulate
  progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
```

## Prelude to preservation

Three key steps.

The first step is to show that types are preserved by _renaming_.

_Renaming_:
Let `Γ` and `Δ` be two contexts such that every variable that
appears in `Γ` also appears with the same type in `Δ`.  Then
if any term is typeable under `Γ`, it has the same type under `Δ`.

In symbols:

    ∀ {x A} → Γ ∋ x ⦂ A  →  Δ ∋ x ⦂ A
    ---------------------------------
    ∀ {M A} → Γ ⊢ M ⦂ A  →  Δ ⊢ M ⦂ A

Three important corollaries follow.  The _weaken_ lemma asserts that a term
which is well typed in the empty context is also well typed in an arbitrary
context.  The _drop_ lemma asserts that a term which is well typed in a context
where the same variable appears twice remains well typed if we drop the shadowed
occurrence. The _swap_ lemma asserts that a term which is well typed in a
context remains well typed if we swap two variables.

The second step is to show that types are preserved by
_substitution_.

_Substitution_:
Say we have a closed term `V` of type `A`, and under the
assumption that `x` has type `A` the term `N` has type `B`.
Then substituting `V` for `x` in `N` yields a term that
also has type `B`.

In symbols:

    ∅ ⊢ V ⦂ A
    Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
    Γ ⊢ N [ x := V ] ⦂ B

The result does not depend on `V` being a value, but it does
require that `V` be closed.

The lemma establishes that substitution composes well with typing:
typing the components separately guarantees that the result of
combining them is also well typed.

The third step is to show preservation.

_Preservation_:
If `∅ ⊢ M ⦂ A` and `M —→ N` then `∅ ⊢ N ⦂ A`.

## Renaming

```agda
ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z = Z
ext ρ (S x≠y loc) = S x≠y (ρ loc)
```

With the extension lemma under our belts, it is straightforward to
prove renaming preserves types:
```agda
rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` x) = ⊢` (ρ x)
rename ρ (⊢ƛ typ) = ⊢ƛ (rename (ext ρ) typ)
rename ρ (typ · typ′) = (rename ρ typ) · (rename ρ typ′)
rename ρ ⊢zero = ⊢zero
rename ρ (⊢suc typ) = ⊢suc (rename ρ typ)
rename ρ (⊢case typ typ′ typ″) =
  ⊢case (rename ρ typ) (rename ρ typ′) (rename (ext ρ) typ″)
rename ρ (⊢μ typ) = ⊢μ (rename (ext ρ) typ)
```

Important corr:

First, a closed term can be weakened to any context:
```agda
weaken : ∀ {Γ M A}  → ∅ ⊢ M ⦂ A → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C} → ∅ ∋ z ⦂ C → Γ ∋ z ⦂ C
  ρ ()
```

```agda
drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z = Z
  ρ (S x Z) = contradiction refl x
  ρ (S x (S x₁ loc)) = S x loc
```
```agda
swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z = S x≢y Z
  ρ (S x Z) = Z
  ρ (S x (S x₁ loc)) = S x₁ (S x loc)
```

## Substitution

The key to preservation – and the trickiest bit of the proof – is
the lemma establishing that substitution preserves types.

```agda
subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes x≡y = weaken ⊢V
... | no  x≢y = contradiction refl x≢y
subst {x = y} ⊢V (⊢` {x = x} (S x≢y x∈Γ)) with x ≟ y
... | yes x≡y = contradiction x≡y x≢y
... | no  x≢y = ⊢` x∈Γ
subst {x = y} ⊢V (⊢ƛ {x = x} N⦂B) with x ≟ y
... | yes refl = ⊢ƛ (drop N⦂B)
... | no  x≢y = ⊢ƛ (subst ⊢V (swap x≢y N⦂B))
subst {x = y} ⊢V (N⦂B · M⦂C) = (subst ⊢V N⦂B) · (subst ⊢V M⦂C)
subst {x = y} ⊢V ⊢zero = ⊢zero
subst {x = y} ⊢V (⊢suc N⦂B) = ⊢suc (subst ⊢V N⦂B)
subst {x = y} ⊢V (⊢case {x = x} N⦂B N⦂B₁ N⦂B₂) with x ≟ y
... | yes refl = ⊢case (subst ⊢V N⦂B) (subst ⊢V N⦂B₁) (drop N⦂B₂)
... | no  x≢y = ⊢case (subst ⊢V N⦂B) (subst ⊢V N⦂B₁) (subst ⊢V (swap x≢y N⦂B₂))
subst {x = y} ⊢V (⊢μ {x = x} N⦂B) with x ≟ y
... | yes refl = ⊢μ (drop N⦂B)
... | no  x≢y  = ⊢μ (subst ⊢V (swap x≢y N⦂B))
```

## Preservation

```agda
preserve : ∀ {M N A} → ∅ ⊢ M ⦂ A → M —→ N → ∅ ⊢ N ⦂ A
preserve (⊢L · ⊢M) (ξ-·₁ steps) = preserve ⊢L steps · ⊢M
preserve (⊢L · ⊢M) (ξ-·₂ x steps) = ⊢L · preserve ⊢M steps
preserve (⊢ƛ ⊢L · ⊢M) (β-ƛ x) = subst ⊢M ⊢L
preserve (⊢suc ⊢M) (ξ-suc steps) = ⊢suc (preserve ⊢M steps)
preserve (⊢case ⊢M ⊢M₁ ⊢M₂) (ξ-case steps) = ⊢case (preserve ⊢M steps) ⊢M₁ ⊢M₂
preserve (⊢case ⊢zero ⊢M₁ ⊢M₂) β-zero = ⊢M₁
preserve (⊢case (⊢suc ⊢M) ⊢M₁ ⊢M₂) (β-suc x) = subst ⊢M ⊢M₂
preserve (⊢μ ⊢M) β-μ = subst (⊢μ ⊢M) ⊢M
```

## Evaluation

```agda
sucμ  =  μ "x" ⇒ `suc (` "x")

_ =
  begin
    sucμ
  —→⟨ β-μ ⟩
    `suc sucμ
  —→⟨ ξ-suc β-μ ⟩
    `suc `suc sucμ
  —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc `suc `suc sucμ
  --  ...
  ∎
```
Since every Agda computation must terminate,
we cannot simply ask Agda to reduce a term to a value.
Instead, we will provide a natural number to Agda, and permit it

By analogy, we will use the name _gas_ for the parameter which puts a
bound on the number of reduction steps.  `Gas` is specified by a natural number:
```agda
record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished (N : Term) : Set where
  done :       Value N → Finished N
  out-of-gas :           Finished N
```

Given a term `L` of type `A`, the evaluator will, for some `N`, return
a reduction sequence from `L` to `N` and an indication of whether
reduction finished:
```agda
data Steps (L : Term) : Set where
  steps : ∀ {N} → L —↠ N → Finished N → Steps L
```
The evaluator takes gas and evidence that a term is well typed,
and returns the corresponding steps:
```agda
eval : ∀ {L A} → Gas → ∅ ⊢ L ⦂ A → Steps L
eval {L} (gas zero) ⊢L = steps (L ∎) out-of-gas
eval {L} (gas (suc amount)) ⊢L with progress ⊢L
... | done v = steps (L ∎) (done v)
... | step z with eval (gas amount) (preserve ⊢L z)
...    | steps sts fin = steps (L —→⟨ z ⟩ sts ) fin
```

### Examples

```agda
⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` ∋x))
  where
  ∋x = Z

_ : eval (gas 3) ⊢sucμ ≡
  steps
   (μ "x" ⇒ `suc ` "x"
   —→⟨ β-μ ⟩
    `suc (μ "x" ⇒ `suc ` "x")
   —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ "x" ⇒ `suc ` "x"))
   —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ "x" ⇒ `suc ` "x")))
   ∎)
   out-of-gas
_ = refl
{-
_ : eval (gas 100) (⊢twoᶜ · ⊢sucᶜ · ⊢zero) ≡ {!eval (gas 100) (⊢twoᶜ · ⊢sucᶜ · ⊢zero)!}
_ = {!!}
-}
```

Next, we "show" two plus two is four:

_ : eval (gas 100) ⊢2+2 ≡ {!eval (gas 100) ⊢2+2!}
_ = {!!}

_ : eval (gas 100) ⊢2+2ᶜ ≡ {!eval (gas 100) ⊢2+2ᶜ!}
_ = {!!}


## Well-typed terms don't get stuck

A term is _normal_ if it cannot reduce:
```agda
Normal : Term → Set
Normal M  =  ∀ {N} → ¬ (M —→ N)
```

A term is _stuck_ if it is normal yet not a value:
```agda
Stuck : Term → Set
Stuck M  =  Normal M × ¬ Value M
```

Using progress, it is easy to show that no well-typed term is stuck:
```agda
postulate
  unstuck : ∀ {M A}
    → ∅ ⊢ M ⦂ A
      -----------
    → ¬ (Stuck M)
```

Using preservation, it is easy to show that after any number of steps,
a well-typed term remains well typed:
```agda
postulate
  preserves : ∀ {M N A}
    → ∅ ⊢ M ⦂ A
    → M —↠ N
      ---------
    → ∅ ⊢ N ⦂ A
```

An easy consequence is that starting from a well-typed term, taking
any number of reduction steps leads to a term that is not stuck:
```agda
postulate
  wttdgs : ∀ {M N A}
    → ∅ ⊢ M ⦂ A
    → M —↠ N
      -----------
    → ¬ (Stuck N)
```
Felleisen and Wright, who introduced proofs via progress and
preservation, summarised this result with the slogan _well-typed terms
don't get stuck_. 

## Reduction is deterministic

```agda
cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl
```

```agda
det : ∀ {M M′ M″} → (M —→ M′) → (M —→ M″) → M′ ≡ M″
det {L · M₁} (ξ-·₁ st₁) (ξ-·₁ st₂) = cong (λ z → z · M₁) (det st₁ st₂)
det (ξ-·₁ st₁) (ξ-·₂ x st₂) = contradiction st₁ (V¬—→ x) 
det (ξ-·₂ x st₁) (ξ-·₁ st₂) = contradiction st₂ (V¬—→ x)
det {V · M} (ξ-·₂ x st₁) (ξ-·₂ x₁ st₂) = cong (V ·_) (det st₁ st₂)
det (ξ-·₂ x st₁) (β-ƛ VM) = contradiction VM (—→¬V st₁) 
det (β-ƛ VM) (ξ-·₂ x₁ st₂) = contradiction VM (—→¬V st₂) 
det (β-ƛ x) (β-ƛ x₁) = refl
det (ξ-suc st₁) (ξ-suc st₂) = cong `suc_ (det st₁ st₂)
det (ξ-case st₁) (ξ-case st₂) = cong₄ (case_[zero⇒_|suc_⇒_]) (det st₁ st₂) refl refl refl
det (ξ-case (ξ-suc st₁)) (β-suc x) = contradiction x (—→¬V st₁)
det β-zero β-zero = refl
det (β-suc x) (ξ-case (ξ-suc st₂)) = contradiction x(—→¬V st₂) 
det (β-suc x) (β-suc x₁) = refl
det β-μ β-μ = refl
```

## Unicode

This chapter uses the following unicode:

    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    Δ  U+0394  GREEK CAPITAL LETTER DELTA (\GD or \Delta)
    β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
    δ  U+03B4  GREEK SMALL LETTER DELTA (\Gd or \delta)
    μ  U+03BC  GREEK SMALL LETTER MU (\Gm or \mu)
    ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
    ρ  U+03B4  GREEK SMALL LETTER RHO (\Gr or \rho)
    ᵢ  U+1D62  LATIN SUBSCRIPT SMALL LETTER I (\_i)
    ᶜ  U+1D9C  MODIFIER LETTER SMALL C (\^c)
    –  U+2013  EM DASH (\em)
    ₄  U+2084  SUBSCRIPT FOUR (\_4)
    ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
    ∅  U+2205  EMPTY SET (\0)
    ∋  U+220B  CONTAINS AS MEMBER (\ni)
    ≟  U+225F  QUESTIONED EQUAL TO (\?=)
    ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
    ⦂  U+2982  Z NOTATION TYPE COLON (\:)
