import Mathlib

/-- IMO 2007 Problem 5: if 4ab - 1 divides (4a^2 - 1)^2 for positive integers a and b,
then a = b. -/
def root_stmt : Prop :=
  ∀ a b : ℤ, 0 < a → 0 < b → (4 * a * b - 1) ∣ (4 * a ^ 2 - 1) ^ 2 → a = b
