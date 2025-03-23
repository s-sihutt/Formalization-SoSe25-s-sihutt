-- This is a Lean file.

-- Here are some sample Lean codes.

-- Here is a simple iterated sum:
#eval Id.run do
  let mut sum := 0
  for i in List.range 101 do
    sum := sum + i
  return sum

-- Here is the definition of the Fibonacci function:
#check 0
  def fib : Nat → Nat
  | 0     => 1
  | 1     => 1
  | n + 2 => fib n + fib (n + 1)

-- We can use #eval to get the 13th Fibonacci number:
#eval fib 13
