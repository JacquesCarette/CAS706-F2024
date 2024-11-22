```agda
module CAS706.part2.Confluence where
```

## Introduction

Confluence / Church-Rosser property / Diamond

Property of relations. The usual property is on "one step" relations,
and this doesn't work for our lambda calculus:

    (λ x. x x)((λ x. x) a) —→ (λ x. x x) a
    (λ x. x x)((λ x. x) a) —→ ((λ x. x) a) ((λ x. x) a)

Both terms can reduce to `a a`, but the second term requires two steps
to get there, not one.

Solution: parallel reduction.

## Imports

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function.Base using (_∘_)
open import Data.Product.Base using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import CAS706.part2.Substitution as Substitution using (Rename; Subst)
open import CAS706.part2.Untyped
  using (_—→_; β; ξ₁; ξ₂; ζ; _—↠_; begin_; _—→⟨_⟩_; _—↠⟨_⟩_; _∎;
  abs-cong; appL-cong; appR-cong; —↠-trans;
  _⊢_; _∋_; `_; #_; _,_; ★; ƛ_; _·_; _[_];
  rename; ext; exts; Z; S_; subst; subst-zero; Context)
```

## Parallel Reduction

```agda
infix 2 _⇛_

data _⇛_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  pvar : ∀{Γ A}{x : Γ ∋ A}
      ---------
    → (` x) ⇛ (` x)

  pabs : ∀{Γ}{N N′ : Γ , ★ ⊢ ★}
    → N ⇛ N′
      ----------
    → ƛ N ⇛ ƛ N′

  papp : ∀{Γ}{L L′ M M′ : Γ ⊢ ★}
    → L ⇛ L′
    → M ⇛ M′
      -----------------
    → L · M ⇛ L′ · M′

  pbeta : ∀{Γ}{N N′  : Γ , ★ ⊢ ★}{M M′ : Γ ⊢ ★}
    → N ⇛ N′
    → M ⇛ M′
      -----------------------
    → (ƛ N) · M  ⇛  N′ [ M′ ]
```
The first three rules are congruences that reduce each of their
parts simultaneously. The last rule reduces a lambda term and
term in parallel followed by a beta step.

We remark that the `pabs`, `papp`, and `pbeta` rules perform reduction
on all their subexpressions simultaneously. Also, the `pabs` rule is
akin to the `ζ` rule and `pbeta` is akin to `β`.

Parallel reduction is reflexive.

```agda
par-refl : ∀{Γ A}{M : Γ ⊢ A} → M ⇛ M
par-refl = {!!}

infix  2 _⇛*_
infixr 2 _⇛⟨_⟩_
infix  3 _∎

data _⇛*_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      --------
    → M ⇛* M

  _⇛⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ⇛ M
    → M ⇛* N
      ---------
    → L ⇛* N
```

## Equivalence between parallel reduction and reduction

```agda
beta-par : ∀{Γ A}{M N : Γ ⊢ A} → M —→ N → M ⇛ N
beta-par red = {!!}

betas-pars : ∀{Γ A} {M N : Γ ⊢ A} → M —↠ N → M ⇛* N
betas-pars reds = {!!}
```

(important to remember abs-cong, appL-cong and apR-cong here)
```agda
par-betas : ∀{Γ A}{M N : Γ ⊢ A} → M ⇛ N → M —↠ N
par-betas preds = {!!}

pars-betas : ∀{Γ A} {M N : Γ ⊢ A} → M ⇛* N → M —↠ N
pars-betas (M₁ ∎) = M₁ ∎
pars-betas (L ⇛⟨ p ⟩ ps) = —↠-trans (par-betas p) (pars-betas ps)
```


## Substitution lemma for parallel reduction

Our next goal is to prove the diamond property for parallel
reduction. But to do that, we need to prove that substitution
respects parallel reduction. That is, if
`N ⇛ N′` and `M ⇛ M′`, then `N [ M ] ⇛ N′ [ M′ ]`.
We cannot prove this directly by induction, so we
generalize it to: if `N ⇛ N′` and
the substitution `σ` pointwise parallel reduces to `τ`,
then `subst σ N ⇛ subst τ N′`.

```agda
par-subst : ∀{Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
par-subst {Γ}{Δ} σ σ′ = ∀{A}(x : Γ ∋ A) → σ x ⇛ σ′ x
```

Import some stuff from Substitution:
```agda
rename-subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{ρ : Rename Γ Δ }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {N = N} = Substitution.rename-subst-commute {N = N}

par-rename : ∀{Γ Δ A} {ρ : Rename Γ Δ} {M M′ : Γ ⊢ A}
  → M ⇛ M′  → rename ρ M ⇛ rename ρ M′
par-rename pvar = pvar
par-rename (pabs p) = pabs (par-rename p)
par-rename (papp p₁ p₂) = papp (par-rename p₁) (par-rename p₂)
par-rename {Γ}{Δ}{A}{ρ} (pbeta{Γ}{N}{N′}{M}{M′} p₁ p₂) =
  {!pbeta (par-rename {ρ = ext ρ} p₁) (par-rename {ρ = ρ} p₂)!}

par-subst-exts : ∀{Γ Δ} {σ τ : Subst Γ Δ}
  → par-subst σ τ
    ------------------------------------------
  → ∀{B} → par-subst (exts σ {B = B}) (exts τ)
par-subst-exts s = {!!}


subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{σ : Subst Γ Δ }
  → subst (exts σ) N [ subst σ M ] ≡ subst σ (N [ M ])
subst-commute {N = N} = Substitution.subst-commute {N = N}

subst-par : ∀{Γ Δ A} {σ τ : Subst Γ Δ} {M M′ : Γ ⊢ A}
  → par-subst σ τ  →  M ⇛ M′
    --------------------------
  → subst σ M ⇛ subst τ M′
subst-par {M = ` x} s pvar = s x
subst-par {M = ƛ N} s (pabs p) =       pabs (subst-par (par-subst-exts s) p)
subst-par {M = L · M} s (papp p₁ p₂) = papp (subst-par s p₁) (subst-par s p₂)
subst-par {Γ}{Δ}{★}{σ}{τ}{(ƛ N) · M} s (pbeta{N′ = N′}{M′ = M′} p₁ p₂)
    with pbeta (subst-par{σ = exts σ}{τ = exts τ}{M = N}
                        (par-subst-exts s) p₁)
               (subst-par {σ = σ} s p₂)
... | G rewrite subst-commute{N = N′}{M = M′}{σ = τ} = G
```
(I twiddle things, and the `rewrite` broke, and I spent an hour fixing it!)

```agda
par-subst-zero : ∀{Γ}{A}{M M′ : Γ ⊢ A}
       → M ⇛ M′
       → par-subst (subst-zero M) (subst-zero M′)
par-subst-zero p Z = p
par-subst-zero p (S x) = pvar
```

We conclude this section with the desired corollary, that substitution
respects parallel reduction.

```agda
sub-par : ∀{Γ A B} {N N′ : Γ , A ⊢ B} {M M′ : Γ ⊢ A}
  → N ⇛ N′
  → M ⇛ M′
    --------------------------
  → N [ M ] ⇛ N′ [ M′ ]
sub-par pn pm = subst-par (par-subst-zero pm) pn
```

## Parallel reduction satisfies the diamond property

The heart of the confluence proof is made of stone, or rather, of
diamond!  We show that parallel reduction satisfies the diamond
property: that if `M ⇛ N` and `M ⇛ N′`, then `N ⇛ L` and `N′ ⇛ L` for
some `L`.  The typical proof is an induction on `M ⇛ N` and `M ⇛ N′`
so that every possible pair gives rise to a witness `L` given by
performing enough beta reductions in parallel.

However, a simpler approach is to perform as many beta reductions in
parallel as possible on `M`, say `M ⁺`, and then show that `N` also
parallel reduces to `M ⁺`. The desired property may be illustrated as

        M
       /|
      / |
     /  |
    N   2
     \  |
      \ |
       \|
        M⁺

where downward lines are instances of `⇛`, so we call it the _triangle
property_.

```agda
_⁺ : ∀ {Γ A}
  → Γ ⊢ A → Γ ⊢ A
(` x) ⁺       =  ` x
(ƛ M) ⁺       = ƛ (M ⁺)
((ƛ N) · M) ⁺ = N ⁺ [ M ⁺ ]
(L · M) ⁺     = L ⁺ · (M ⁺)

par-triangle : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ⇛ N
    -------
  → N ⇛ M ⁺
par-triangle pvar          = pvar
par-triangle (pabs p)      = pabs (par-triangle p)
par-triangle (pbeta p1 p2) = sub-par (par-triangle p1) (par-triangle p2)
par-triangle (papp {L = ƛ _ } (pabs p1) p2) =
  pbeta (par-triangle p1) (par-triangle p2)
par-triangle (papp {L = ` _}   p1 p2) = papp (par-triangle p1) (par-triangle p2)
par-triangle (papp {L = _ · _} p1 p2) = papp (par-triangle p1) (par-triangle p2)
```

The proof of the triangle property is an induction on `M ⇛ N`.

* Suppose `x ⇛ x`. Clearly `x ⁺ = x`, so `x ⇛ x ⁺`.



The diamond property then follows by halving the diamond into two triangles.

        M
       /|\
      / | \
     /  |  \
    N   2   N′
     \  |  /
      \ | /
       \|/
        M⁺

That is, the diamond property is proved by applying the
triangle property on each side with the same confluent term `M ⁺`.

```agda
par-diamond : ∀{Γ A} {M N N′ : Γ ⊢ A}
  → M ⇛ N
  → M ⇛ N′
    ---------------------------------
  → Σ[ L ∈ Γ ⊢ A ] (N ⇛ L) × (N′ ⇛ L)
par-diamond {M = M} p1 p2 = ⟨ M ⁺ , ⟨ par-triangle p1 , par-triangle p2 ⟩ ⟩
```

## Proof of confluence for parallel reduction

As promised at the beginning, the proof that parallel reduction is
confluent is easy now that we know it satisfies the triangle property.
We just need to prove the strip lemma, which states that
if `M ⇛ N` and `M ⇛* N′`, then
`N ⇛* L` and `N′ ⇛ L` for some `L`.
The following diagram illustrates the strip lemma

        M
       / \
      1   *
     /     \
    N       N′
     \     /
      *   1
       \ /
        L

where downward lines are instances of `⇛` or `⇛*`, depending on how
they are marked.

The proof of the strip lemma is a straightforward induction on `M ⇛* N′`,
using the triangle property in the induction step.

```agda
strip : ∀{Γ A} {M N N′ : Γ ⊢ A}
  → M ⇛ N
  → M ⇛* N′
    ------------------------------------
  → Σ[ L ∈ Γ ⊢ A ] (N ⇛* L)  ×  (N′ ⇛ L)
strip mn many = {!!}
```

The proof of confluence for parallel reduction is now proved by
induction on the sequence `M ⇛* N`, using the above lemma in the
induction step.

```agda
par-confluence : ∀{Γ A} {L M₁ M₂ : Γ ⊢ A}
  → L ⇛* M₁
  → L ⇛* M₂
    ------------------------------------
  → Σ[ N ∈ Γ ⊢ A ] (M₁ ⇛* N) × (M₂ ⇛* N)
par-confluence many-1 many-2 = {!!}
```

The step case may be illustrated as follows:

            L
           / \
          1   *
         /     \
        M₁ (a)  M₂
       / \     /
      *   *   1
     /     \ /
    M₁′(b)  N
     \     /
      *   *
       \ /
        N′

## Proof of confluence for reduction

```agda
confluence : ∀{Γ A} {L M₁ M₂ : Γ ⊢ A}
  → L —↠ M₁
  → L —↠ M₂
    -----------------------------------
  → Σ[ N ∈ Γ ⊢ A ] (M₁ —↠ N) × (M₂ —↠ N)
confluence L↠M₁ L↠M₂ = {!!}
```


## Notes

This mechanized proof of confluence is loosely based on several
sources including @Schafer:2015, @Takahashi:1995, @Pfenning:1992, and
Nipkow and Berghofer's mechanization in Isabelle, which is based on a
paper by @Nipkow:1996.

## Unicode

This chapter uses the following unicode:

    ⇛  U+21DB  RIGHTWARDS TRIPLE ARROW (\r== or \Rrightarrow)
    ⁺  U+207A  SUPERSCRIPT PLUS SIGN   (\^+)
