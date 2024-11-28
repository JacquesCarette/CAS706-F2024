```agda
module CAS706.part2.BigStep where
```

## Introduction

call-by-name is deterministic, i.e.
produces a value if and only if beta reduction can reduce
the program to a lambda abstraction.

Here: forward. Backwards in part3 because 'syntactic' proof very hard.

We present the call-by-name strategy as a relation between an input
term and an output value. Such a relation is often called a _big-step
semantics_, written `M ⇓ V`, as it relates the input term `M` directly
to the final result `V`.

## Imports

```agda
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong-app)
open import Data.Product.Base using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Function.Base using (_∘_)
open import CAS706.part2.Untyped
  using (Context; _⊢_; _∋_; ★; ∅; _,_; Z; S_; `_; #_; ƛ_; _·_;
  subst; subst-zero; exts; rename; β; ξ₁; ξ₂; ζ; _—→_; _—↠_; _—→⟨_⟩_; _∎;
  —↠-trans; appL-cong)
open import CAS706.part2.Substitution as Substitution using (Subst; ids)
```

## Environments

To handle variables and function applications, there is the choice
between using substitution, as in `—→`, or to use an _environment_.
An environment in call-by-name is a map from variables to closures,
that is, to terms paired with their environments. We choose to use
environments instead of substitution because the point of the
call-by-name strategy is to be closer to an implementation of the
language. Also, the denotational semantics introduced in later
chapters uses environments and the proof of adequacy
is made easier by aligning these choices.

```agda
ClosEnv : Context → Set

data Clos : Set where
  clos : ∀{Γ} → (M : Γ ⊢ ★) → ClosEnv Γ → Clos

ClosEnv Γ = ∀ (x : Γ ∋ ★) → Clos

-- empty and extension:
∅' : ClosEnv ∅
∅' ()

_,'_ : ∀ {Γ} → ClosEnv Γ → Clos → ClosEnv (Γ , ★)
(γ ,' c) Z = c
(γ ,' c) (S x) = γ x
```

## Big-step evaluation

The big-step semantics is represented as a ternary relation,
written `γ ⊢ M ⇓ V`, where `γ` is the environment, `M` is the input
term, and `V` is the result value.  A _value_ is a closure whose term
is a lambda abstraction.

```agda
data _⊢_⇓_ : ∀{Γ} → ClosEnv Γ → (Γ ⊢ ★) → Clos → Set where

  ⇓-var : ∀{Γ}{γ : ClosEnv Γ}{x : Γ ∋ ★}{Δ}{δ : ClosEnv Δ}{M : Δ ⊢ ★}{V}
    → γ x ≡ clos M δ
    → δ ⊢ M ⇓ V
      -----------
    → γ ⊢ ` x ⇓ V

  ⇓-lam : ∀{Γ}{γ : ClosEnv Γ}{M : Γ , ★ ⊢ ★}
    → γ ⊢ ƛ M ⇓ clos (ƛ M) γ

  ⇓-app : ∀{Γ}{γ : ClosEnv Γ}{L M : Γ ⊢ ★}{Δ}{δ : ClosEnv Δ}{N : Δ , ★ ⊢ ★}{V}
    → γ ⊢ L ⇓ clos (ƛ N) δ   →   (δ ,' clos M γ) ⊢ N ⇓ V
      ---------------------------------------------------
    → γ ⊢ L · M ⇓ V
```

* The `⇓-var` rule evaluates a variable by finding the associated
  closure in the environment and then evaluating the closure.

* The `⇓-lam` rule turns a lambda abstraction into a closure
  by packaging it up with its environment.

* The `⇓-app` rule performs function application by first evaluating
  the term `L` in operator position. If that produces a closure containing
  a lambda abstraction `ƛ N`, then we evaluate the body `N` in an
  environment extended with the argument `M`. Note that `M` is not
  evaluated in rule `⇓-app` because this is call-by-name and not
  call-by-value.

## The big-step semantics is deterministic

```agda
⇓-determ : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{V V' : Clos}
  → γ ⊢ M ⇓ V → γ ⊢ M ⇓ V'
  → V ≡ V'
⇓-determ (⇓-var x v) (⇓-var x₁ v') with refl ← trans (sym x) x₁ = ⇓-determ v v'
⇓-determ ⇓-lam ⇓-lam = refl
⇓-determ (⇓-app v₀ v₁) (⇓-app v₂ v₃) with refl ← ⇓-determ v₀ v₂ = ⇓-determ v₁ v₃
```


## Big-step evaluation implies beta reduction to a lambda

If big-step evaluation produces a value, then the input term can
reduce to a lambda abstraction by beta reduction:

      ∅' ⊢ M ⇓ clos (ƛ N′) δ
      -----------------------------
    → Σ[ N ∈ ∅ , ★ ⊢ ★ ] (M —↠ ƛ N)

To get there, we'll need to strenghten the actual conclusion (twice).

We make the two notions of equivalence precise by defining the
following two mutually-recursive predicates `V ≈ M` and `γ ≈ₑ σ`.

```agda
_≈_ : Clos → (∅ ⊢ ★) → Set
_≈ₑ_ : ∀{Γ} → ClosEnv Γ → Subst Γ ∅ → Set

(clos {Γ} M γ) ≈ N = Σ[ σ ∈ Subst Γ ∅ ] (γ ≈ₑ σ) × (N ≡ subst σ M)

γ ≈ₑ σ = ∀ x → (γ x) ≈ (σ x)
```

We can now state the main lemma:

    If γ ⊢ M ⇓ V  and  γ ≈ₑ σ,
    then  subst σ M —↠ N  and  V ≈ N  for some N.

```agda
≈ₑ-id : ∅' ≈ₑ ids
≈ₑ-id ()

sub-id : ∀{Γ} {A} {M : Γ ⊢ A} → subst ids M ≡ M
sub-id = Substitution.sub-id
```


We define an auxiliary function for extending a substitution.

```agda
ext-subst : ∀{Γ Δ} → Subst Γ Δ → Δ ⊢ ★ → Subst (Γ , ★) Δ
ext-subst σ N = subst (subst-zero N) ∘ exts σ
```

The next lemma we need to prove states that if you start with an
equivalent environment and substitution `γ ≈ₑ σ`, extending them with
an equivalent closure and term `V ≈ N` produces an equivalent
environment and substitution: `(γ ,' V) ≈ₑ (ext-subst σ N)`,
or equivalently, `(γ ,' V) x ≈ (ext-subst σ N) x` for any
variable `x`. The proof will be by induction on `x` and
for the induction step we need the following lemma,
which states that applying the composition of `exts σ`
and `subst-zero` to `S x` is the same as just `σ x`,
which is a corollary of a theorem in
Chapter [Substitution](/Substitution/).

```agda
subst-zero-exts : ∀{Γ Δ}{σ : Subst Γ Δ}{B}{M : Δ ⊢ B}{x : Γ ∋ ★}
  → (subst (subst-zero M) ∘ exts σ) (S x) ≡ σ x
subst-zero-exts {Γ}{Δ}{σ}{B}{M}{x} =
   cong-app (Substitution.subst-zero-exts-cons{σ = σ}) (S x)

≈ₑ-ext : ∀ {Γ} {γ : ClosEnv Γ} {σ : Subst Γ ∅} {V} {N : ∅ ⊢ ★}
  → γ ≈ₑ σ  →  V ≈ N
    --------------------------
  → (γ ,' V) ≈ₑ (ext-subst σ N)
≈ₑ-ext γ≈ₑσ V≈N loc = {!!}
```

To prove the main lemma, we need another technical lemma about
substitution. Applying one substitution after another is the same as
composing the two substitutions and then applying them.

```agda
sub-sub : ∀{Γ Δ Σ}{A}{M : Γ ⊢ A} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ}
  → subst σ₂ (subst σ₁ M) ≡ subst (subst σ₂ ∘ σ₁) M
sub-sub {M = M} = Substitution.sub-sub {M = M}
```

We arrive at the main lemma: if `M` big steps to a
closure `V` in environment `γ`, and if `γ ≈ₑ σ`, then `subst σ M` reduces
to some term `N` that is equivalent to `V`. We describe the proof
below.

```agda
⇓→—↠×≈ : ∀{Γ}{γ : ClosEnv Γ}{σ : Subst Γ ∅}{M : Γ ⊢ ★}{V : Clos}
       → γ ⊢ M ⇓ V  →  γ ≈ₑ σ
         ---------------------------------------
       → Σ[ N ∈ ∅ ⊢ ★ ] (subst σ M —↠ N) × V ≈ N
⇓→—↠×≈ {γ = γ} (⇓-var{x = x} γx≡Lδ δ⊢L⇓V) γ≈ₑσ
    with γ x | γ≈ₑσ x | γx≡Lδ
... | clos L δ | ⟨ τ , ⟨ δ≈ₑτ , σx≡τL ⟩ ⟩ | refl
      with ⇓→—↠×≈{σ = τ} δ⊢L⇓V δ≈ₑτ
...   | ⟨ N , ⟨ τL—↠N , V≈N ⟩ ⟩ rewrite σx≡τL =
        ⟨ N , ⟨ τL—↠N , V≈N ⟩ ⟩
⇓→—↠×≈ {σ = σ} {V = clos (ƛ N) γ} (⇓-lam) γ≈ₑσ =
    ⟨ subst σ (ƛ N) , ⟨ subst σ (ƛ N) ∎ , ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ ⟩ ⟩
⇓→—↠×≈{Γ}{γ} {σ = σ} {L · M} {V} (⇓-app {N = N} L⇓ƛNδ N⇓V) γ≈ₑσ
    with ⇓→—↠×≈{σ = σ} L⇓ƛNδ γ≈ₑσ
... | ⟨ _ , ⟨ σL—↠ƛτN , ⟨ τ , ⟨ δ≈ₑτ , ≡ƛτN ⟩ ⟩ ⟩ ⟩ rewrite ≡ƛτN
      with ⇓→—↠×≈ {σ = ext-subst τ (subst σ M)} N⇓V
             (λ x → ≈ₑ-ext{σ = τ} δ≈ₑτ ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ x)
           | β{∅}{subst (exts τ) N}{subst σ M}
...   | ⟨ N' , ⟨ —↠N' , V≈N' ⟩ ⟩ | ƛτN·σM—→
        rewrite sub-sub{M = N}{σ₁ = exts τ}{σ₂ = subst-zero (subst σ M)} =
        let rs = (ƛ subst (exts τ) N) · subst σ M —→⟨ ƛτN·σM—→ ⟩ —↠N' in
        let g = —↠-trans (appL-cong σL—↠ƛτN) rs in
        ⟨ N' , ⟨ g , V≈N' ⟩ ⟩
```



With the main lemma complete, we establish the forward direction
of the equivalence between the big-step semantics and beta reduction.

```agda
cbn→reduce :  ∀{M : ∅ ⊢ ★}{Δ}{δ : ClosEnv Δ}{N′ : Δ , ★ ⊢ ★}
  → ∅' ⊢ M ⇓ clos (ƛ N′) δ
    -----------------------------
  → Σ[ N ∈ ∅ , ★ ⊢ ★ ] (M —↠ ƛ N)
cbn→reduce {M}{Δ}{δ}{N′} M⇓c
    with ⇓→—↠×≈{σ = ids} M⇓c ≈ₑ-id
... | xx = {!!}





















{-
... | ⟨ N , ⟨ rs , ⟨ σ , ⟨ h , eq2 ⟩ ⟩ ⟩ ⟩ rewrite sub-id{M = M} | eq2 =
      ⟨ subst (exts σ) N′ , rs ⟩
-}
```

## Beta reduction to a lambda implies big-step evaluation

(skippin even the idea - read the book if you're curious)

## Unicode

This chapter uses the following unicode:

    ≈  U+2248  ALMOST EQUAL TO (\~~ or \approx)
    ₑ  U+2091  LATIN SUBSCRIPT SMALL LETTER E (\_e)
    ⊢  U+22A2  RIGHT TACK (\|- or \vdash)
    ⇓  U+21DB  DOWNWARDS DOUBLE ARROW (\d= or \Downarrow)
