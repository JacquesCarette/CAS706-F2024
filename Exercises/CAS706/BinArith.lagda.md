This is the "model" solution for the binary arithmetic exercises, and
will be used in A3.

```agda
module CAS706.BinArith where

open import Data.Nat.Base using (ℕ; zero; suc)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (m O) = m I
inc (m I) = inc m O

dbl : ℕ → ℕ
dbl zero = zero
dbl (suc m) = suc (suc (dbl m))

tob : ℕ → Bin
tob zero = ⟨⟩
tob (suc m) = inc (tob m)

fromb : Bin → ℕ
fromb ⟨⟩ = 0
fromb (n O) = dbl (fromb n)
fromb (n I) = suc (dbl (fromb n))

dblb : Bin → Bin
dblb ⟨⟩ = ⟨⟩
dblb (m O) = m O O
dblb (m I) = m I O
```
