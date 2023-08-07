module plfa.part1.Part1 where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

infixl 6  _+_

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)