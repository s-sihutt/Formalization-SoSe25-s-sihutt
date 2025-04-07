import Mathlib.Tactic
-- This is a Lean file.

-- Here are some sample Lean codes.

-- Fundamentally Lean is a functional programming language.
-- That means it can be used for completely standard programming.

-- We can define functions in Lean directly:
def linear_combo (x y : ℕ ) : ℕ := 3*x + 4*y

def implicit_linear_combo (x y : ℕ) := 3*x + 4*y

#eval linear_combo 2 3
#eval implicit_linear_combo 2 3

-- We can define functions in Lean via pattern matching.
def made_up_function : ℕ → ℕ
| 0     => 1
| 1     => 5
| _     => 7

def made_up_function' : ℕ → ℕ
| 0     => 1
| 1     => 5
| _     => 7

#eval made_up_function 9

-- In fact we can use pattern matching to define function recursively.
def fib : ℕ → ℕ
  | 0     => 1
  | 1     => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 13

-- We can use recursion to do some cool things.

#check Bool
#check true
#check false

def even : ℕ → Bool
  | 0     => true
  | n + 1 => not (even n)

def odd : ℕ  → Bool
  | 0     => false
  | n + 1 => not (odd n)

#eval even 6
#eval even 9

#eval odd 13
#eval odd 8

#check and

def mystery : ℕ → Bool := fun n => and (even n) (odd n)

#eval mystery 7
#eval mystery 8


-- We can also define lists in Lean.

#check List -- Notice lists need to have a type!
#check List Nat -- Now we have a list of natural numbers.

-- We can define lists of natural numbers:
def random_list : List Nat := [3, 22, 38, 25, 7]
#eval random_list

def range_list : List Nat := List.range 10
#eval range_list

-- We can extract elements from lists
#eval range_list[7]
#eval random_list[2]

-- We can also apply functions to lists.
#eval (random_list.map odd)

-- Here is a simple iterated sum:
#eval Id.run do
  let mut sum := 0
  for i in List.range 101 do
    sum := sum + i
  return sum

-- This is the end of the standard programming part.

-- Let's start with some mathematics.

-- Here is something crucial: There are identity types.
-- They check if two things are equal.
#check 3 = 4

-- Everything is equal to itself.
#check rfl
#check (@rfl _ 3)
#check (@rfl _ Bool)
#check (@rfl _ List)
#check (@rfl _ Type)

-- We already saw natural numbers.
#check ℕ

-- What we didn't see, natural numbers satisfy rules.
#check Nat.add_comm
#check Nat.add_assoc
#check Nat.mul_comm

-- FUNDAMENTAL FACT: These are all functions!
#check Nat.add_comm _ 4



def maybe_too_complicated : 2 + (3 + 4) = 4 + (2 + 3) := Nat.add_comm 4 (2 + 3) ▸ Eq.symm (Nat.add_assoc 2 3 4)

def wasnt_too_complicated : 2 + (3 + 4) = 4 + (2 + 3) := Eq.refl (2 + (3 + 4))  ▸ Eq.symm (Nat.add_assoc 2 3 4)

variable (a b c : ℕ)

theorem exercise : a + b = b + a := Nat.add_comm a b

def too_complicated : a + (b + c) = c + (a + b) := Nat.add_comm c (a + b) ▸ Eq.symm (Nat.add_assoc a b c)

-- This is getting complicated! We want:
--  Tactics!
--  Interactcitivity!

def still_easy : 2 + (3 + 4) = 4 + (2 + 3) := by
  rfl

def now_easy : a + (b + c) = c + (a + b) := by
  rw [Nat.add_comm c (a+b)]
  rw [Nat.add_assoc a b c]

def even_easier : a + (b + c) = c + (a + b) := by
  rw [Nat.add_comm c (a+b)]
  rw [Nat.add_assoc]

def further_easier : a + (b + c) = c + (a + b) := by
  rw [Nat.add_comm c (a+b), Nat.add_assoc]

def easiest : a + (b + c) = c + (a + b) := by
  ring

-- Tactics are great! But they don't solve everything!
def FermatLastTheorem := ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

theorem FermatLastTheoremHolds : FermatLastTheorem := by sorry
