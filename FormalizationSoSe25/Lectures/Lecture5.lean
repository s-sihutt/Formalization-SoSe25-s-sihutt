import Mathlib.Tactic


section review


/-
Last time we saw some logic and set theory.

Negation:
* How to define `¬ P`
* Relevant tactics:
  - `exfalso` - to prove `P` from `False`
  - `by_contra` - to prove by contradiction
  - `contradiction` - as a more efficient version

Set Theory:
* We defined the type of subsets `Set X`
* We saw it comes with many algebraic operations:
  - `∩` - intersection
  - `∪` - union
  - `\` - set difference
  - `⊆` - subset

* We saw the tactic `ext` to prove to sets are equal.

* For a function `f : X → Y` we defined the preimage and image.
  - `Set.preimage f A` or `f ⁻¹' A` - preimage of `A`
  - `Set.image f A` or `f '' A` - image of `A`

* Functions have many properties:
  - `Injective` - one-to-one
  - `Surjective` - onto
  - `Bijective` - one-to-one and onto

* We can define injective, surjective and bijective functions on a particular set.
  - `Set.InjOn` - injective on a set
  - `Set.SurjOn` - surjective on a set
  - `Set.BijOn` - bijective on a set

* Finally, we saw some more advanced aspects of set theory:
  - The axiom of choice
  - The Cantor theorem

-/
end review

section question
-- Here is an answer:

variable (X : Type) (Y : Type) (f : X → Y)
#check (∀ ⦃x₁ : X⦄, x₁ ∈ Set.univ → ∀ ⦃x₂ : X⦄, x₂ ∈ Set.univ → f x₁ = f x₂ → x₁ = x₂)

end question

section rintro
/-
We have seen the `intro` tactic, which introduces a hypothesis.
We can use `obtain` more efficiently.
We can also use `rintro`, which is a more powerful version of `intro`.
-/

-- Let's see an example that should be familiar.
example (P Q R : Prop) : (P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (Q ∧ R) := by
  constructor
  intro hpqr
  · obtain ⟨hpq, hr⟩ := hpqr
    rcases hpq with hp | hq
    · simp [hp, hr]
    · simp [hq, hr]
  intro hpqr
  · obtain hpr | hqr := hpqr
    · obtain ⟨hp, hr⟩ := hpr
      simp [hp, hr]
    · obtain ⟨hq, hr⟩ := hqr
      simp [hq, hr]

example (P Q R : Prop) : (P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (Q ∧ R) := by
  constructor
  intro hpqr
  · obtain ⟨hpq, hr⟩ := hpqr
    -- We can phrase everything with `obtain`
    obtain hp | hq := hpq
    · simp [hp, hr]
    · simp [hq, hr]
  intro hpqr
  · obtain hpr | hqr := hpqr
    · obtain ⟨hp, hr⟩ := hpr
      simp [hp, hr]
    · obtain ⟨hq, hr⟩ := hqr
      simp [hq, hr]

example (P Q R : Prop) : (P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (Q ∧ R) := by
  constructor
  intro hpqr
  -- We can combine the `obtain`
  obtain ⟨ hp | hq , hr⟩ := hpqr
  · simp [hp, hr]
  · simp [hq, hr]
  intro hpqr
  -- We can combine the `obtain`
  obtain ⟨hp, hr⟩ | ⟨hq, hr⟩ := hpqr
  · simp [hp, hr]
  · simp [hq, hr]

-- We can also use `rcases` instead of `obtain`.
example (P Q R : Prop) : (P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (Q ∧ R) := by
  constructor
  intro hpqr
  -- We can combine the `rcases`
  rcases hpqr with ⟨ hp | hq , hr⟩
  · simp [hp, hr]
  · simp [hq, hr]
  intro hpqr
  -- We can combine the `rcases`
  rcases hpqr with ⟨hp, hr⟩ | ⟨hq, hr⟩
  · simp [hp, hr]
  · simp [hq, hr]

-- We now introduce `rintro`!
-- It combines `intro` and `obtain` or `rcases`.
example (P Q R : Prop) : (P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (Q ∧ R) := by
  constructor
  rintro ⟨ hp | hq , hr⟩
  · simp [hp, hr]
  · simp [hq, hr]
  rintro (⟨hp, hr⟩ | ⟨hq, hr⟩)
  · simp [hp, hr]
  · simp [hq, hr]

end rintro

section namespaces
/-
We saw we can use more advanced definitions and results with `dot` notation.

So, `Injective` is a property of functions, and hence needs a `Function.` before.
-/
#check Set.InjOn
#check Function.Injective

/- In the long run this is very inconvenient. What we want is more efficient code!
For that we use `namespace`-/

open Function
-- This opens the `namespace` for `Function`.
#check Injective

open Set
-- This opens the `namespace` for `Set`.
#check InjOn

-- Namespaces *automatically* stay open in the section and
-- close with the closing of the section!
end namespaces

section namespaces2

-- #check Injective

-- One can open multiple namespaces at once.
open Function Set

#check Injective
#check univ
#check InjOn

end namespaces2

section testuniverses
/-
Lean has a hierarchy of universes.
By default, the lowest one is `Type 0` or just `Type`.
-/
variable (X : Type)
variable (X' : Type 0)
#check X
#check X'
#check Type

-- There are higher universes.
variable (Y : Type 1)
#check Y
#check Type 1

variable (n : Nat)
variable (Z : Type n)
#check Z
#check Type n

universe u v w

#check Type u
variable (A : Type u)
variable (B : Type v)
#check  A × B

variable (C : Type*)
#check C
#check C × A

/-
In most cases these universe considerations are not relevant.
But some times thing are subtle.
-/

#check X
#check Y

-- Here is the easy case we knew:
def XX' : Type := X × X'

-- Here things can get tricky:
def XY : Type 1 := X × Y
-- def XY' : Type := X × Y
-- def XY'' : Type* := X × Y
def XY''' : Type _ := X × Y

#check XY'''
end testuniverses

section structures

/-
In mathematics we layer structures to study more
complicated objects and ideas:
* A group is a set with operations ...
* A ringt is a set with operations ...
* A topological spaces is a set with ...
* A metric space is a set with ...
* A vector space is a set with ...

We know what a set is in Lean, a `Type`.
But what are structures?
We want to *structure* our types!
-/

-- We can define a structure in Lean using the `structure` keyword.

@[ext]
structure new_pair where
  x : Nat
  y : Nat

#check new_pair
#check new_pair.x -- projection to first component
#check new_pair.y -- projection to second component


/-
We can create new instances via:
* `newpair.mk x y` which stands for *make*
* A tuple `⟨x , y⟩`
* `where` notation
-/


example : new_pair := new_pair.mk 1 2

-- We can also explicitly provide the input names:
example : new_pair := new_pair.mk (x := 1) (y := 2)

example : new_pair := new_pair.mk (y := 1) (x := 2)

example : new_pair := ⟨1, 2⟩

example : new_pair where
  x := 1
  y := 2

-- These three approaches results in the same object.
example : new_pair.mk 1 2 = (⟨1, 2⟩ : new_pair) := by rfl

-- `new_pair` satisfies extensionality.
-- For `structure` the tactic `cases` is very useful.
-- We can use `cases` to deconstructs the object.

example (x₁ y₁ x₂ y₂ : Nat) : new_pair.mk x₁ y₁ = new_pair.mk x₂ y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · intro h
    cases h
    simp
  · intro ⟨eqx, eqy⟩
    rw [eqx, eqy]

-- By adding the `@[ext]` attribute we can use the tactic `ext` to prove equality.
example (x₁ y₁ x₂ y₂ : Nat) : new_pair.mk x₁ y₁ = new_pair.mk x₂ y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · intro h
    cases h
    simp
  · intro ⟨eqx, eqy⟩
    ext
    · rw [eqx]
    · rw [eqy]

-- Of course when all data are just two points, this does not help too much.


-- We can now define functions on `new_pair`, the way we did before.
example (_ : new_pair) : new_pair := by
  constructor
  · exact 3
  · exact 4

example (_ : new_pair) : new_pair := ⟨3 ,4⟩

/-
Here is a problem:
We want to define standard operations on `new_pair`.
Like `add`, `mul`, etc.
This requires creating a new `namespace`.
-/
--

namespace new_pair

def add (a b : new_pair) : new_pair :=
  ⟨a.x + b.x, a.y + b.y⟩

def add' (a b : new_pair) : new_pair where
  x := a.x + b.x
  y := a.y + b.y

example : new_pair := add (⟨2, 3⟩) (⟨1, 4⟩)

def mul (a b : new_pair) : new_pair :=
  ⟨a.x * b.x, a.y * b.y⟩

#check add_comm

def add_comm (a b : new_pair) : add a b = add b a := by
  ext
  · simp [add]
    ring
  · simp [add]
    ring

end new_pair

-- Now outside the namespace we can use these operations
-- via `new_pair.add` and `new_pair.mul`.
#check new_pair.add
#check new_pair.mul
#check new_pair.add_comm

end structures

section pointed_types
-- Let's see a more difficult example, just to get a sense what Lean is capable of.

-- A `pointed type` is a type with a distinguished term.
structure PointedType where
  carrier : Type*
  pt : carrier

#print PointedType
#check PointedType.{0}

-- We can do a `coercion` to associate to a `PointedType` a `Type` in an implicit manner.
instance : CoeSort PointedType Type* := ⟨fun α ↦ α.carrier⟩

-- Here is a example defined for `Type`
def product (X : Type) : Type :=
  X × X

-- We can hence define operations on `PointedType` whenever the input is a `Type`.
#check product (PointedType.mk ℕ 0)

-- Working with `PointedType` is a bit more complicated.
example (X Y : Type) (x : X) ( y : Y) : PointedType.mk X x = PointedType.mk Y y ↔ ∃ (h : X = Y), h ▸ x = y := by
  constructor
  · intro h
    cases h
    simp
  · intro ⟨h, eq⟩
    simp
    constructor
    · rw [h]
    · subst h
      simp at eq
      rw [eq]

/-
Similar to `PointedType`, we can define a `PointedFunction`
as a function between `PointedType` that preserves the distinguished point.
-/
structure PointedFunction (X Y : PointedType) where
  toFun : X → Y
  toFun_pt : toFun X.pt = Y.pt

-- We can even define new notation for `PointedFunction`.
infix:50 " →. " => PointedFunction

-- Similar to types, we can coerce `PointedFunction` to a  `Function`.
instance {X Y : PointedType} : CoeFun (X →. Y) (fun _ ↦ X → Y) := ⟨fun e ↦ e.toFun⟩

-- This tells the pretty printer to print the operation with `↑`.
attribute [coe] PointedFunction.toFun

namespace PointedFunction

variable {X Y Z : PointedType}

-- The `@[simp]` attribute tells Lean to use this lemma in `simp` tactics.
@[simp] lemma coe_pt (f : X →. Y) : f X.pt = Y.pt := f.toFun_pt

-- We can use simp to construct the composition.
def comp (g : Y →. Z) (f : X →. Y) : X →. Z :=
  { toFun := g ∘ f
    toFun_pt := by simp}

end PointedFunction

/-
Now, for two pointed functions we can take the regular composition
`Function.comp` and the pointed composition `PointedFunction.comp`.
-/

variable (X Y Z : PointedType) (f : X →. Y) (g : Y →. Z)

#check Function.comp g f
#check PointedFunction.comp g f

end pointed_types
