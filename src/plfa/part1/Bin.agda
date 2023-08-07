module plfa.part1.Bin where

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

eleven : Bin
eleven = ⟨⟩ I O I I

-- strategy : ripple up carry
inc : Bin → Bin
inc ⟨⟩ = ⟨⟩               -- (1) lhs exit case
inc (bs O) = bs I         -- (2) inductive case on rhs 0     → inc in place and no carry
inc (⟨⟩ I) = ⟨⟩ I O       -- (3) iff rhs 1 then enlarge size → dec in place and write carry
inc (bs I) = (inc bs) O   -- (4) inductive case on rhs 1     → dec in place and carry

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_ : inc (⟨⟩ O) ≡ ⟨⟩ I
_ =
  begin
    inc (⟨⟩ O)
  ≡⟨⟩ -- case 2
    ⟨⟩ I
  ∎

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ =
  begin
    inc (⟨⟩ I)
  ≡⟨⟩ -- case 3
    ⟨⟩ I O
  ∎

_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ =
  begin
    inc (⟨⟩ I O)
  ≡⟨⟩ -- case 2
    ⟨⟩ I I
  ∎

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ =
  begin
    inc (⟨⟩ I I)
  ≡⟨⟩ -- case 4
    (inc (⟨⟩ I)) O
  ≡⟨⟩ -- case 3
    ⟨⟩ I O O
  ∎

_ : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
_ =
  begin
    inc (⟨⟩ I O O)
  ≡⟨⟩ -- case 2
    ⟨⟩ I O I
  ∎
