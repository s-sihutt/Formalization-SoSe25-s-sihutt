-- Here is a first `import Mathlib.Tactic` to get things started.
-- Based on the definitions you need, you can add more imports right below.
import Mathlib.Tactic
-- Theoretically, you could just write `import Mathlib`, but this will be somewhat slower.

/- Remember we can open namespaces to shorten names and enable notation.

For example (feel free to change it): -/
open Function Set

/- Remember if many new definitions require a `noncomputable` either in the `section` or definition.

For example (feel free to change it): -/
noncomputable section

/- You can now start writing definitions and theorems. -/
