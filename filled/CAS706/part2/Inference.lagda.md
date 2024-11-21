```agda
module CAS706.part2.Inference where
```

Let's write fewer types (i.e. top-level only) and not full
derivations.

_bidirectional_ type inference

## Introduction: Inference rules as algorithms {#algorithms}

    (ƛ x ⇒ x) ⦂ (A ⇒ A)

holds for _every_ type `A`.

What small language where every term has a unique type.

    L, M, N ::=                         decorated terms
      x                                   variable
      ƛ x ⦂ A ⇒ N                         abstraction (decorated)
      L · M                               application

Each of the associated type rules can be read as an algorithm for
type checking.  For each typing judgment, we label each position
as either an _input_ or an _output_.

    Γ ∋ x ⦂ A

`Γ`, `x` inputs `A`, output.

    ----------------- Z
    Γ , x ⦂ A ∋ x ⦂ A

    Γ ∋ x ⦂ A
    ----------------- S
    Γ , y ⦂ B ∋ x ⦂ A

(clockwise reading)





    Γ ⊢ M ⦂ A

`Γ`, `M` inputs, `A` output
Syntax directed

    Γ ∋ x ⦂ A
    -----------
    Γ ⊢ ` x ⦂ A

    Γ , x ⦂ A ⊢ N ⦂ B
    ---------------------------
    Γ ⊢ (ƛ x ⦂ A ⇒ N) ⦂ (A ⇒ B)

    Γ ⊢ L ⦂ A ⇒ B
    Γ ⊢ M ⦂ A′
    A ≡ A′
    -------------
    Γ ⊢ L · M ⦂ B


Moving on to bidirectional:
- break the normal typing judgment into two judgments
  - one that produces the type as an output (as above)
  - one that takes it as an input.


## Synthesising and inheriting types

JC: evil notation.

    Γ ⊢ M ↑ A   - 'synthesize', i.e. 'infer'. Type is output
    Γ ⊢ M ↓ A   - 'inherit', i.e. check. Type is input ("Ok" is output)

Which terms use what?
- _deconstructor_ => synthesis
- _constructors_ => inheritance

"side terms" of deconstructor: inheritance

syntax-directed: break terms into `Term⁺` and `Term⁻`
  Will need new term forms to "turn the arrow around"

The term form `M ↓ A` represents the only place terms need to be
decorated with types.

    L⁺, M⁺, N⁺ ::=                      terms with synthesized type
      x                                   variable
      L⁺ · M⁻                             application
      M⁻ ↓ A                              switch to inherited

    L⁻, M⁻, N⁻ ::=                      terms with inherited type
      ƛ x ⇒ N⁻                            abstraction
      `zero                               zero
      `suc M⁻                             successor
      case L⁺ [zero⇒ M⁻ |suc x ⇒ N⁻ ]     case
      μ x ⇒ N⁻                            fixpoint
      M⁺ ↑                                switch to synthesized

## Soundness and completeness

What we intend to show is that the typing judgments are
_decidable_:

    synthesize : ∀ (Γ : Context) (M : Term⁺)
        ------------------------------------
      → Dec (∃[ A ] Γ ⊢ M ↑ A)

    inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
              --------------------------------------
            → Dec (Γ ⊢ M ↓ A)

success ~ soundness
fail ~ completeness

negative proof ~ semantically verified error message (but not so readable...)

## Imports

f```agda
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.String using (String; _≟_)
open import Data.Product.Base using (_×_; ∃; ∃-syntax; Σ; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Nullary.Decidable using ( Dec; yes; no; False; toWitnessFalse)

import CAS706.part2.More as DB
```

## Syntax

```agda
infix   4  _∋_⦂_
infix   4  _⊢_↑_
infix   4  _⊢_↓_
infixl  5  _,_⦂_

infixr  7  _⇒_

infix   5  ƛ_⇒_
infix   5  μ_⇒_
infix   6  _↑
infix   6  _↓_
infixl  7  _·_
infix   8  `suc_
infix   9  `_
```

```agda
Id : Set
Id = String

data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context
```

The syntax of terms is defined by mutual recursion.
```agda
data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  `_                       : Id → Term⁺
  _·_                      : Term⁺ → Term⁻ → Term⁺
  _↓_                      : Term⁻ → Type → Term⁺

data Term⁻ where
  ƛ_⇒_                     : Id → Term⁻ → Term⁻
  `zero                    : Term⁻
  `suc_                    : Term⁻ → Term⁻
  `case_[zero⇒_|suc_⇒_]    : Term⁺ → Term⁻ → Id → Term⁻ → Term⁻
  μ_⇒_                     : Id → Term⁻ → Term⁻
  _↑                       : Term⁺ → Term⁻
```

## Example terms

```agda
two : Term⁻
two = `suc (`suc `zero)

plus : Term⁺
plus = (μ "p" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          `case (` "m") [zero⇒ ` "n" ↑
                        |suc "m" ⇒ `suc (` "p" · (` "m" ↑) · (` "n" ↑) ↑) ])
            ↓ (`ℕ ⇒ `ℕ ⇒ `ℕ)

2+2 : Term⁺
2+2 = plus · two · two

Ch : Type
Ch = (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ

twoᶜ : Term⁻
twoᶜ = (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑)

plusᶜ : Term⁺
plusᶜ = (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
           ` "m" · (` "s" ↑) · (` "n" · (` "s" ↑) · (` "z" ↑) ↑) ↑)
             ↓ (Ch ⇒ Ch ⇒ Ch)

sucᶜ : Term⁻
sucᶜ = ƛ "x" ⇒ `suc (` "x" ↑)

2+2ᶜ : Term⁺
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
```

## Bidirectional type checking

```agda
data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A} → Γ , x ⦂ A ∋ x ⦂ A
  S : ∀ {Γ x y A B} → x ≢ y → Γ ∋ x ⦂ A
    → Γ , y ⦂ B ∋ x ⦂ A
```

```agda
data _⊢_↑_ : Context → Term⁺ → Type → Set
data _⊢_↓_ : Context → Term⁻ → Type → Set

data _⊢_↑_ where

  ⊢` : ∀ {Γ A x}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ↑ A

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ↑ A ⇒ B
    → Γ ⊢ M ↓ A
      -------------
    → Γ ⊢ L · M ↑ B

  ⊢↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓ A
      ---------------
    → Γ ⊢ (M ↓ A) ↑ A

data _⊢_↓_ where

  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ↓ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ↓ A ⇒ B

  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ↓ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ↓ `ℕ
      ---------------
    → Γ ⊢ `suc M ↓ `ℕ

  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ↑ `ℕ
    → Γ ⊢ M ↓ A
    → Γ , x ⦂ `ℕ ⊢ N ↓ A
      -------------------------------------
    → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ↓ A

  ⊢μ : ∀ {Γ x N A}
    → Γ , x ⦂ A ⊢ N ↓ A
      -----------------
    → Γ ⊢ μ x ⇒ N ↓ A

  ⊢↑ : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≡ B
      -------------
    → Γ ⊢ (M ↑) ↓ B
```

## Prerequisites

The rule for `M ↑` requires the ability to decide whether two types
are equal.
```agda
_≟Tp_ : (A B : Type) → Dec (A ≡ B)
`ℕ ≟Tp `ℕ = yes refl
`ℕ ≟Tp (s ⇒ t) = no λ ()
(s ⇒ t) ≟Tp `ℕ = no λ ()
(s ⇒ t) ≟Tp (x ⇒ y) with s ≟Tp x | t ≟Tp y
... | no ¬s≡x | _ = no λ { refl → contradiction refl ¬s≡x }
... | yes s≡x | no ¬t≡y = no λ { refl → contradiction refl ¬t≡y }
... | yes s≡x | yes t≡y = yes (cong₂ _⇒_ s≡x t≡y)

dom≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
dom≡ refl = refl

rng≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
rng≡ refl = refl

ℕ≢⇒ : ∀ {A B} → `ℕ ≢ A ⇒ B
ℕ≢⇒ ()
```


## Unique types

```agda
uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
uniq-∋ Z Z                 =  refl
uniq-∋ Z (S x≢y _)         =  contradiction refl x≢y
uniq-∋ (S x≢y _) Z         =  contradiction refl x≢y
uniq-∋ (S _ ∋x) (S _ ∋x′)  =  uniq-∋ ∋x ∋x′
```

```agda
uniq-↑ : ∀ {Γ M A B} → Γ ⊢ M ↑ A → Γ ⊢ M ↑ B → A ≡ B
uniq-↑ (⊢` x) (⊢` y) = uniq-∋ x y
uniq-↑ (lft · x) (rgt · y) = rng≡ (uniq-↑ lft rgt)
uniq-↑ (⊢↓ x) (⊢↓ y) = refl
```

## Lookup type of a variable in the context

lemma lets us 'extend' failure all the way.
```agda
ext∋ : ∀ {Γ B x y}  → x ≢ y → ¬ (∃[ A ] Γ ∋ x ⦂ A)
  → ¬ (∃[ A ] Γ , y ⦂ B ∋ x ⦂ A)
ext∋ x≢y witness ⟨ A , Z ⟩ = contradiction refl x≢y
ext∋ x≢y witness ⟨ A , S x pos ⟩ = contradiction ⟨ A , pos ⟩ witness

lookup : ∀ (Γ : Context) (x : Id) → Dec (∃[ A ] Γ ∋ x ⦂ A)
lookup ∅ x = no λ ()
lookup (ctx , y ⦂ A) x with x ≟ y
... | yes refl = yes ⟨ A , Z ⟩
... | no ¬x≡y  with lookup ctx x
...    | yes ⟨ B , pos ⟩  = yes ⟨ B , S ¬x≡y pos ⟩
...    | no  nowhere = no (ext∋ ¬x≡y nowhere)
```

## Promoting negations

For each possible term form, we need to show that if one of its
components fails to type, then the whole fails to type. Easy
most of the time, but still worth pulling out (and a couple are
tricky).

```agda
¬arg : ∀ {Γ A B L M} → Γ ⊢ L ↑ A ⇒ B → ¬ Γ ⊢ M ↓ A
  → ¬ (∃[ B′ ] Γ ⊢ L · M ↑ B′)
¬arg ⊢L ¬M↓ ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬M↓ ⊢M′ 

¬switch : ∀ {Γ M A B} → Γ ⊢ M ↑ A → A ≢ B
  → ¬ Γ ⊢ (M ↑) ↓ B
¬switch ⊢M A≢B (⊢↑ ⊢M′ A′≡B) rewrite uniq-↑ ⊢M ⊢M′ = contradiction A′≡B A≢B
```

## Synthesize and inherit types

```agda
synthesize : ∀ (Γ : Context) (M : Term⁺) → Dec (∃[ A ] Γ ⊢ M ↑ A )
inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type) → Dec (Γ ⊢ M ↓ A)
```

Here we need to carefully synthesize or inherit the pieces, according to
their 'variance':
```agda
synthesize Γ (` x) with lookup Γ x
... | yes ⟨ A , x⦂A ⟩ = yes ⟨ A , ⊢` x⦂A ⟩
... | no  x∉Γ = no \ { ⟨ A , ⊢` x⦂A ⟩ → contradiction ⟨ A , x⦂A ⟩ x∉Γ }
synthesize Γ (t · s) with synthesize Γ t
... | no ¬t↑A        = no λ { ⟨ B , t↑C · _ ⟩ → ¬t↑A ⟨ _ , t↑C ⟩ }
... | yes ⟨ `ℕ , t↑ℕ ⟩      = no λ { ⟨ A , t↑A⇒B · s↓ ⟩ → ℕ≢⇒ (uniq-↑ t↑ℕ t↑A⇒B) }
... | yes ⟨ A ⇒ B , t↑A⇒B ⟩ with inherit Γ s A
...     | yes s↓A = yes ⟨ B , t↑A⇒B · s↓A ⟩
...     | no ¬s↓A = no (¬arg t↑A⇒B ¬s↓A)
synthesize Γ (t ↓ A) with inherit Γ t A
... | yes t⦂A = yes ⟨ A , ⊢↓ t⦂A ⟩
... | no  ¬t⦂A = no λ { ⟨ B , ⊢↓ x ⟩ → contradiction x ¬t⦂A }

inherit Γ (ƛ x ⇒ trm) `ℕ = no λ ()
inherit Γ (ƛ x ⇒ trm) (A ⇒ B) with inherit (Γ , x ⦂ A) trm B
... | yes pf = yes (⊢ƛ pf)
... | no  ¬chk = no λ { (⊢ƛ chk) → contradiction chk ¬chk }
inherit Γ `zero `ℕ = yes ⊢zero
inherit Γ `zero (typ ⇒ typ₁) = no λ ()
inherit Γ (`suc trm) `ℕ with inherit Γ trm `ℕ
... | yes trm⦂ℕ = yes (⊢suc trm⦂ℕ)
... | no ¬trm⦂ℕ = no λ { (⊢suc x) → ¬trm⦂ℕ x}
inherit Γ (`suc trm) (typ ⇒ typ₁) = no λ ()
inherit Γ `case x [zero⇒ zer |suc y ⇒ sc ] typ with synthesize Γ x
... | no ¬x⊢A = no λ { (⊢case ⊢z⦂A _ _) → ¬x⊢A ⟨ `ℕ , ⊢z⦂A ⟩}
... | yes ⟨ _ ⇒ _ , ⊢L ⟩ = no λ { (⊢case ⊢L′ _ _) → ℕ≢⇒ (uniq-↑ ⊢L′ ⊢L)} 
... | yes ⟨ `ℕ , x⦂ℕ ⟩ with inherit Γ zer typ
...    | no ¬zer⊢A = no λ { (⊢case _ zer⦂A _) → contradiction zer⦂A ¬zer⊢A}
...    | yes zer⦂A with inherit (Γ , y ⦂ `ℕ) sc typ
...        | no ¬sc⊢A = no λ { (⊢case _ _ sc⊢A) → contradiction sc⊢A ¬sc⊢A}
...        | yes sc⦂A = yes (⊢case x⦂ℕ zer⦂A sc⦂A)
inherit Γ (μ x ⇒ trm) typ with inherit (Γ , x ⦂ typ) trm typ
... | no ¬trm⦂typ = no λ { (⊢μ xx) → contradiction xx ¬trm⦂typ}
... | yes xx = yes (⊢μ xx)
inherit Γ (x ↑) typ with synthesize Γ x
... | no ¬x⦂A        = no λ { (⊢↑ x↑A refl) → ¬x⦂A ⟨ typ , x↑A ⟩}
... | yes ⟨ A , x⦂A ⟩ with A ≟Tp typ
...     | yes refl = yes (⊢↑ x⦂A refl)
...     | no A≢typ = no (¬switch x⦂A A≢typ)
```

## Testing the example terms

```
S′ : ∀ {Γ x y A B} → {x≢y : False (x ≟ y)} → Γ ∋ x ⦂ A
   → Γ , y ⦂ B ∋ x ⦂ A
S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x
```

## Testing the error cases

Unbound variable:
```agda
_ : synthesize ∅ ((ƛ "x" ⇒ ` "y" ↑) ↓ (`ℕ ⇒ `ℕ)) ≡ no _
_ = refl
```

Argument in application is ill typed:
```agda
_ : synthesize ∅ (plus · sucᶜ) ≡ no _
_ = refl
```

Function in application is ill typed:
```agda
_ : synthesize ∅ (plus · sucᶜ · two) ≡ no _
_ = refl
```

Function in application has type natural:
```agda
_ : synthesize ∅ ((two ↓ `ℕ) · two) ≡ no _
_ = refl
```

Abstraction inherits type natural:
```agda
_ : synthesize ∅ (twoᶜ ↓ `ℕ) ≡ no _
_ = refl
```

Zero inherits a function type:
```agda
_ : synthesize ∅ (`zero ↓ `ℕ ⇒ `ℕ) ≡ no _
_ = refl
```

Successor inherits a function type:
```agda
_ : synthesize ∅ (two ↓ `ℕ ⇒ `ℕ) ≡ no _
_ = refl
```

Successor of an ill-typed term:
```agda
_ : synthesize ∅ (`suc twoᶜ ↓ `ℕ) ≡ no _
_ = refl
```

Case of a term with a function type:
```agda
_ : synthesize ∅
      ((`case (twoᶜ ↓ Ch) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡ no _
_ = refl
```

Case of an ill-typed term:
```agda
_ : synthesize ∅
      ((`case (twoᶜ ↓ `ℕ) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡ no _
_ = refl
```

Inherited and synthesised types disagree in a switch:
```agda
_ : synthesize ∅ (((ƛ "x" ⇒ ` "x" ↑) ↓ `ℕ ⇒ (`ℕ ⇒ `ℕ))) ≡ no _
_ = refl
```


## Erasure

It is easy to define an _erasure_ function that takes an extrinsic
type judgment into the corresponding intrinsically-typed term.

```agda
∥_∥Tp : Type → DB.Type
∥ `ℕ ∥Tp             =  DB.`ℕ
∥ A ⇒ B ∥Tp          =  ∥ A ∥Tp DB.⇒ ∥ B ∥Tp

∥_∥Cx : Context → DB.Context
∥ ∅ ∥Cx              =  DB.∅
∥ Γ , x ⦂ A ∥Cx      =  ∥ Γ ∥Cx DB., ∥ A ∥Tp

∥_∥∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ∥ Γ ∥Cx DB.∋ ∥ A ∥Tp
∥ Z ∥∋               =  DB.Z
∥ S x≢ ∋x ∥∋         =  DB.S ∥ ∋x ∥∋

∥_∥⁺ : ∀ {Γ M A} → Γ ⊢ M ↑ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp
∥_∥⁻ : ∀ {Γ M A} → Γ ⊢ M ↓ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp

∥ ⊢` ⊢x ∥⁺           =  DB.` ∥ ⊢x ∥∋
∥ ⊢L · ⊢M ∥⁺         =  ∥ ⊢L ∥⁺ DB.· ∥ ⊢M ∥⁻
∥ ⊢↓ ⊢M ∥⁺           =  ∥ ⊢M ∥⁻

∥ ⊢ƛ ⊢N ∥⁻           =  DB.ƛ ∥ ⊢N ∥⁻
∥ ⊢zero ∥⁻           =  DB.`zero
∥ ⊢suc ⊢M ∥⁻         =  DB.`suc ∥ ⊢M ∥⁻
∥ ⊢case ⊢L ⊢M ⊢N ∥⁻  =  DB.case ∥ ⊢L ∥⁺ ∥ ⊢M ∥⁻ ∥ ⊢N ∥⁻
∥ ⊢μ ⊢M ∥⁻           =  DB.μ ∥ ⊢M ∥⁻
∥ ⊢↑ ⊢M refl ∥⁻      =  ∥ ⊢M ∥⁺
```

## Bidirectional inference in Agda

Agda itself uses bidirectional inference.  This explains why
constructors can be overloaded while other defined names cannot ---
here by _overloaded_ we mean that the same name can be used for
constructors of different types.  Constructors are typed by
inheritance, and so the type is available when resolving the
constructor, whereas variables are typed by synthesis, and so each
variable must have a unique type.

Most top-level definitions in Agda are of functions, which are typed
by inheritance, which is why Agda requires a type declaration for
those definitions.  A definition with a right-hand side that is a term
typed by synthesis, such as an application, does not require a type
declaration.
```agda
answer = 6 * 7
```


## Unicode

This chapter uses the following unicode:

    ↓  U+2193:  DOWNWARDS ARROW (\d)
    ↑  U+2191:  UPWARDS ARROW (\u)
    ∥  U+2225:  PARALLEL TO (\||)
