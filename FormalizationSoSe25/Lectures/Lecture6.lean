import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.HasLimits

section review


/-
Last time we discussed three topics:

1. The value of `rintro`.

2. How Lean deals with `universes`.

3. How we can define structures in Lean.

-/

end review

section projects

/-
There are two options to proceed:
1. Regular option: Check the website.
2. Hard option: Talk to me.
-/

end projects

section mathlib
/-
Let's learn a little about `MathLib`
`MathLib` is the standard mathematical library for Lean4.
It contains most of the mathematics formalized in Lean4.
Part of setting up this project involved installing `MathLib`.

A single Lean file does not contain any particular definitions.
We hence load existing definitions from `MathLib` to use them in our file.
We include them in the beginning of the file using `import`.

For example, if you notice, every file until now has the first line:
`import Mathlib.Tactic`.

This loads `tactics` and various standard definitions and theorems from `MathLib`.

Let us see some examples.
-/

#check Group
#check Ring
#check Field
#check TopologicalSpace
#check MetricSpace
#check CategoryTheory.Category
#check ULift

-- If we go more specialized, we need more imports.
-- Here is an example from limits in category theory.
#check CategoryTheory.Limits.HasLimits

/-
Working on a project will mean familiarizing yourself with certain parts of `MathLib`,
relevant to your project.
-/
end mathlib

section groups_as_structures

-- `Groups` have already been defined in `MathLib`.
#check Group
-- We can unwind the definition.
#print Group
-- Let us try to reproduce such a definition by hand.

-- Here is a hands-on definition of a group:
structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one
  mul_inv_cancel : ∀ x : α, mul x (inv x) = one

-- We can now as an example define the integers as a group:
def group_z : Group₁ ℤ where
  mul x y := x + y
  one := 0
  inv x := -x
  mul_assoc _ _ _ := add_assoc _ _ _
  one_mul := zero_add
  mul_one := add_zero
  inv_mul_cancel := fun _ => by ring
  mul_inv_cancel := fun _ => by ring

-- We can now use this group structure on `ℤ`:
#check group_z.mul
#check group_z.inv_mul_cancel
#check group_z.mul 2 (-3)

-- We can (for example) see that `ℤ` with the group structure `group_z` is commutative:
example (a b : ℤ) : group_z.mul a b = group_z.mul b a := by
  simp [group_z]
  ring

/-
We can use this approach to define any structure
(groups, rings, fields, topological spaces, etc.) in Lean.

However, this approach diverges from standard mathematical practice.

For example, we just write `ℝ` and the additional structure should be recognizable from the context.
-/



#check ℝ
-- In this line `ℝ` is a `group`:
#check (2 : ℝ) + (3 : ℝ)
#check Add.add (2 : ℝ) (3 : ℝ)
-- Here `ℝ` is a `field`:
#check (5 : ℝ) * (0.2 : ℝ)
-- Here `ℝ` is a `topological space` or maybe a `metric space`:
variable (f : ℝ → ℝ)
#check Continuous f

/-
If we followed our approach above, every one of these statements would require
explicitly stating the group structure, field structure, topology, etc.

Fortunately, there is a computer scientific solution in Lean.
Those are `classes` and `instances`.
-/
end groups_as_structures

section groups_as_classes
/-
We want to try to understand `structures`, `classes`, and `instances` in Lean.
In particular, the powerful tool of `type class inference`.

Let us restate a structure, we had seen before:
-/

def GroupR : Group₁ ℝ where
  mul x y := x + y
  one := 0
  inv x := -x
  mul_assoc _ _ _ := add_assoc _ _ _
  one_mul := zero_add
  mul_one := add_zero
  inv_mul_cancel := fun _ => by ring
  mul_inv_cancel := fun _ => by ring
/-
This definition is clearly the worst and we always have to
*remember* and *use* the name of the structure `GroupR`.
-/

#check Group₁.mul GroupR (2:ℝ) (3: ℝ)

-- Lean knows what this structure is, because of `GroupR`.
example (x y : ℝ) : Group₁.mul GroupR x y = x + y := by
  rfl

#eval Group₁.mul GroupR (2:ℝ) (3:ℝ)

/-
We have seen before we can add `tags` to structures.
One such tag is `@[class]`.
-/

@[class] structure Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one
  mul_inv_cancel : ∀ x : α, mul x (inv x) = one

/-
The `@[class]` tag tells Lean that this structure is a `class`.
This means that we can use `type class inference` to find the structure.
Concretely, we now structures as an `instance`.
We can then access the structure via `inferInstance`.
-/

instance : Group₂ ℝ where
  mul x y := x + y
  one := 0
  inv x := -x
  mul_assoc _ _ _ := add_assoc _ _ _
  one_mul := zero_add
  mul_one := add_zero
  inv_mul_cancel := fun _ => by ring
  mul_inv_cancel := fun _ => by ring

#check Group₂.mul inferInstance (2:ℝ) (3:ℝ)

/-
We can add the option `trace.Meta.synthInstance true`
to see how Lean finds the instance.
-/

set_option trace.Meta.synthInstance true in
#check Group₂.mul inferInstance (2:ℝ) (3:ℝ)

-- Even though we just wrote `inferInstance`, Lean knows what the operation is
example (x y : ℝ) : Group₂.mul inferInstance x y = x + y := by
  rfl

#eval Group₂.mul inferInstance (2:ℝ) (3:ℝ)

/-
That's a much easier than before, because we dont have to remember
and use the name of the structure `GroupR`.

However, this is still not what we usually do in mathematics.
We simply don't state any structure and just use the operations.

For that reason there is `class` which:
- a structure with the `@[class]` tag
- makes instances implicit.
-/

class Group₃ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one
  mul_inv_cancel : ∀ x : α, mul x (inv x) = one

instance : Group₃ ℝ where
  mul x y := x + y
  one := 0
  inv x := -x
  mul_assoc _ _ _ := add_assoc _ _ _
  one_mul := zero_add
  mul_one := add_zero
  inv_mul_cancel := fun _ => by ring
  mul_inv_cancel := fun _ => by ring


#check Group₁.mul GroupR (2:ℝ) (3:ℝ)
#check Group₂.mul (inferInstance : Group₂ ℝ) (2:ℝ) (3:ℝ)
#check Group₃.mul (2:ℝ) (3:ℝ)

example (x y : ℝ) : Group₃.mul x y = x + y := by
  rfl

#eval Group₃.mul (2:ℝ) (3:ℝ)

-- We assume the existence of classes with `[` `]` brackets.
example (α : Type*) [Group₃ α] (x y : α) : α := Group₃.mul x y
/-
Note here the Group structure is implicit, both
- In the assumption.
- In the parameter of the multiplication operation.
-/


/-
Here are some sample computations using:
- structures
- structures with `@[class]`
- classes
-/

example (α : Type*) (GrpA : Group₁ α) (x y z w : α) : Group₁.mul GrpA (Group₁.mul GrpA x (Group₁.mul GrpA y z)) w = Group₁.mul GrpA (Group₁.mul GrpA x y) (Group₁.mul GrpA z w) := by
  simp [Group₁.mul_assoc]

example (α : Type*) [GrpA : Group₂ α] (x y z w : α) : Group₂.mul GrpA (Group₂.mul GrpA x (Group₂.mul GrpA y z)) w = Group₂.mul GrpA (Group₂.mul GrpA x y) (Group₂.mul GrpA z w) := by
  simp [Group₂.mul_assoc]

example (α : Type*) [Group₃ α] (x y z w : α) : Group₃.mul (Group₃.mul x (Group₃.mul y z)) w = Group₃.mul (Group₃.mul x y) (Group₃.mul z w) := by
  simp [Group₃.mul_assoc]

/-
This last one looks very similar to what we would usually hope for.
We can now even add custom notation and make it even more regular.

Here we use `infixl` to define the notation.
Here `infix` means that the notation is used between two elements.
Then ``infixl` means that the notation is left associative.
This means by definition `x ·₃ y ·₃ z` is interpreted as `x ·₃ (y ·₃ z)`.
The number `60` is the precedence of the operator.
-/

infix:60 " ·₃ "   => Group₃.mul

example (x y : ℝ) : x ·₃ y = x + y := by
  rfl

example (α : Type*) [Group₃ α] (x y z w : α) : (x ·₃ (y ·₃ z)) ·₃ w = (x ·₃ y) ·₃ (z ·₃ w) := by
  simp [Group₃.mul_assoc]

/-
Via instances and suitable notation we can write readable operations,
resembeling regular mathematical notation.

So `+` is just notation for `Add.add`, which is a class for `ℝ`.
-/

#check Add.add

/-
We can now see how all these desired structures are classes:

In this first example we use `AddGroup`, instead of `Group₁`,
as we think of the operation in `Group` by default being multiplication.
-/
example : AddGroup ℝ := inferInstance
example : Ring ℝ := inferInstance
-- Here we use `noncomputable` to construct inverses.
noncomputable example : Field ℝ := inferInstance
example : MetricSpace ℝ := inferInstance
example : TopologicalSpace ℝ := inferInstance

/-
We can now also witness our invented group
structures on `ℝ`:
-/

example : Group₁ ℝ := GroupR
example : Group₂ ℝ := inferInstance
example : Group₃ ℝ := inferInstance

/-
Even beter, for a given instance, we can figure
out the name via the command `#synth`.
-/
#synth AddGroup ℝ
#synth Ring ℝ
#synth Field ℝ
#synth MetricSpace ℝ
#synth TopologicalSpace ℝ
#synth Group₂ ℝ
#synth Group₃ ℝ

#check Real.instRing

/-
Here is a fancier example!
It defines a group structure on the set of self-equivalences.
We might explain this in detail later.
-/
instance {α : Type*} : Group₃ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc _ _ _ := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm
  mul_inv_cancel := Equiv.symm_trans_self

end groups_as_classes

section hierarchies
/-
We have now seen structures, classes, and instances.
Of course, there are many different structures.
Are they related and if yes, how?
The solution is to use `hierarchies`.

Let's try to understand this via an example.

Here is a simple class that assumes add a single term `one`.

Notice here the line `/-- The element one -/` is the doc-string.
That can be used to document the class for users.
-/
class One₁ (α : Type*) where
  /-- The element one -/
  one : α

/- Because of the class we have `[self : One₁ α]` -/
#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

/-
Similar to operations, we can add notation for structures
Here, the tag `@[inherit_doc]`, means it has the same
doc-string as the original definition.
-/
@[inherit_doc]
notation "𝟙" => One₁.one

/- Remember for Lean this is just notation. -/
example {α : Type*} [One₁ α] : α := 𝟙
example {α : Type*} [One₁ α] : (𝟙 : α) = 𝟙 := rfl
example {α : Type*} [One₁ α] : One₁.one = (𝟙 : α) := rfl
/-
You can check here, that `(𝟙 : α)` is necessary
so Lean can infer the type.
-/

/-
We now separately proceed to define a class with a
binary operation, named `dia` for `diamond`.

Our eventual goal is that `𝟙` should be an identity element.
-/
class Dia₁ (α : Type*) where
  /-- Diamond operation -/
  dia : α → α → α

-- We saw before, we can introduce infix notation.
infixl:70 " ⋄ "   => Dia₁.dia

/-
We now have a binary operation, we want to make it associative.
Naively, we could just write out the operation and associativity.
-/
class Semigroup₀ (α : Type*) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

/-
Turns out this is a terrible idea!
The point of `class` is to synthesize instances.
But from this definition, Lean cannot recognize a semigroup.
-/

example {α : Type*} [Dia₁ α] (a b : α) : α := a ⋄ b
-- example {α : Type} [Semigroup₀ α] (a b : α) : α := a ⋄ b

-- Beside `Semigroup₀ α`, we need to add `Dia₁ α` by hand.
example {α : Type*} [Dia₁ α] [Semigroup₀ α] (a b : α) : α := a ⋄ b
/-
This is of course not what we want.
Mathematicaly, we think of `Semigroup₀` as a `Dia₁` with associativity,
meaning we are extending one structure via another.

One possible way to obtain this, is after the fact, add the
relevant connection to the `Dia₁` structure.
We achieve this via `attribute [instance]`.
This tells Lean that `Semigroup₀` is an instance of `Dia₁`.
-/

attribute [instance] Semigroup₀.toDia₁

-- We now have a `Dia₁` instance.
example {α : Type*} [Semigroup₀ α] : Dia₁ α := inferInstance

example {α : Type*} [Semigroup₀ α] (a b : α) : α := a ⋄ b

/-
The better solution is to build in the connection from the start.
We can do this by using `extends` in the definition of `Semigroup₁`.
This means that by definition `Semigroup₁` is a `Dia₁` with associativity.
-/
class Semigroup₂ (α : Type*) extends toDia₁ : Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type*} [Semigroup₂ α] (a b : α) : α := a ⋄ b

/-
Note the `toDia₁` is redundant.
-/

class Semigroup₁ (α : Type*) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

/-
Lean automatically uses `toDia₁`.
Meaning it uses `to` with the previous class name.
-/
#check Semigroup₁.toDia₁

example {α : Type*} [Semigroup₁ α] : Dia₁ α := inferInstance
example {α : Type*} [Semigroup₁ α] (a b : α) : α := a ⋄ b

/-
We now move one step further and add the identity element.
We do this by extending with `Semigroup₁` and `One₁` at the same time.
-/

class DiaOneClass₁ (α : Type*) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

-- In `DiaOneClass₁` we have instances of `One₁ α` and  `Dia₁ α`:
example {α : Type*} [DiaOneClass₁ α] : Dia₁ α := inferInstance
example {α : Type*} [DiaOneClass₁ α] : One₁ α := inferInstance
-- We hence use all the previous operations and definitions:
example {α : Type*} [DiaOneClass₁ α] : α := 𝟙
example {α : Type*} [DiaOneClass₁ α] (a b : α) : α := a ⋄ b

/-
Let's use the `trace.Meta.synthInstance true` option
again to see what is going on.
-/
set_option trace.Meta.synthInstance true in
example {α : Type*} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙


/-
We have almost defined a monoid.
What is missing is combining associativity and the identity element.
We can do this by extending `Semigroup₁` and `DiaOneClass₁`.

The cool fact is that we do not need any additional information:
-/
class Monoid₁ (α : Type*) extends Semigroup₁ α, DiaOneClass₁ α

/-
Here is an interesting fact about this definition:
The `dia` operation is over-determined.
-/

example {α : Type*} [Semigroup₁ α] (a b : α) : α := a ⋄ b
example {α : Type*} [DiaOneClass₁ α] (a b : α) : α := a ⋄ b
example {α : Type*} [Monoid₁ α] (a b : α) : α := a ⋄ b

/-
Part of what `extends` does is to recognize common information
and make sure they coincide.
-/
example {α : Type*} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl

/-
This does not happen if we try to use naive definitions.
For example, here is a more direct definition of a monoid:
-/
class Monoid₂ (α : Type*) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α

-- Now we, can check the following:
-- example {α : Type*} [Monoid₂ α] : (Monoid₂.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₂.toDiaOneClass₁.toDia₁.dia := rfl

/-
Why is everything okay in `Monoid₁` but not in `Monoid₂`?
The reason is that `extends` does not do what we tell it to do!
It has a mind on its own. When writing
`extends Semigroup₁ α, DiaOneClass₁ α`
Lean will check if the two structures have intersections and then remove them.

Let's see how this is done in practice:
-/
#check Monoid₁.mk
#check Monoid₂.mk

/-
Note, this does *not* mean there is no `Monoid₁.toDiaOneClass₁`
-/
#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁

set_option trace.Meta.synthInstance true in
example {α : Type*} [Monoid₁ α] (a b : α) : α := a ⋄ b

/-
We can now define the class `Inv₁` for inverses.
Then extend `Monoid₁` with `Inv₁` to define groups.
-/

class Inv₁ (α : Type*) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₄ (G : Type*) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙
  dia_inv : ∀ a : G, a ⋄ a⁻¹ = 𝟙

/-
We can now start proving facts about groups.
Here is a simple example:
-/
example {M : Type*} [Group₄ M] {a : M} (u :  ∀ b : M, a ⋄ b = b) : a =  𝟙 := by
  calc
    a = a ⋄ 𝟙:= by  rw [DiaOneClass₁.dia_one]
    _ = 𝟙 := by rw [u 𝟙]

/-
As we see, using the various properties of groups is very annoying.
We need to refer to the proper level of the structure.
For example, we write `DiaOneClass₁.dia_one` instead of just `dia_one`.

The solution is to use `export`.
-/

export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₄ (inv_dia dia_inv)

example {M : Type*} [Group₄ M] {a : M} (u :  ∀ b : M, a ⋄ b = b) : a =  𝟙 := by
  calc
    a = a ⋄ 𝟙:= by  rw [dia_one]
    _ = 𝟙 := by rw [u 𝟙]

end hierarchies

section making_implicit_explicit
/-
Let us end with a useful syntax.

When we define functions, then usually the input type and instances are implicit
-/
def gettingid {G: Type*} [Group₄ G] : G := 𝟙

#check gettingid
-- This means we cannot apply anything to `gettingid`.
variable (G : Type*) (h : Group₄ G)
-- None of these options work:
-- #check gettingid G
-- #check gettingid h
-- #check gettingid G h

/-
Whenever we do need to do so,
the solution is to add a `@` in front of the function.
-/
#check @gettingid
#check @gettingid G h

end making_implicit_explicit

/-
We have seen how to define structures, classes, and instances.
We have seen how to use `extends` to build hierarchies.
Next time we discuss morphisms between structures.
-/
