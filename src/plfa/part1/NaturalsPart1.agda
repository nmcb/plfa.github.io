module plfa.part1.NaturalsPart1 where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

infixl 6  _+_

-- day (0) , before C-c C-l
-- _+_ : ℕ → ℕ → ℕ
-- n + m = ?

-- day 1 - before C-c C-c on n
-- _+_ : ℕ → ℕ → ℕ
-- n + m = {!   !}

-- day 2 - before returning m as the base induction step with C-c C-space on hole 0
-- _+_ : ℕ → ℕ → ℕ
-- zero + m = {!   !}
-- suc n + m = {!   !}

-- day 3 - before returning suc (n + m) as the induction step with C-c C-space on hole 1
-- _+_ : ℕ → ℕ → ℕ
-- zero + m = m
-- suc n + m = {!   !}

-- day 4 - after C-c C-l tells us we're 'All Done' <3
_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)
