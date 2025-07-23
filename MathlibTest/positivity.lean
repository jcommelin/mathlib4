import Mathlib.Tactic.Positivity
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Tests for the `positivity` tactic

This tactic proves goals of the form `0 ≤ a` and `0 < a`.
-/
set_option autoImplicit true

open Finset Function Nat NNReal ENNReal

attribute [grind] LT.lt.ne LT.lt.le Eq.le Eq.ge

attribute [grind ←] mul_nonneg add_nonneg
attribute [grind ←] sq_nonneg
attribute [grind ←] _root_.mul_pos _root_.div_pos inv_pos
attribute [grind ←] div_nonneg inv_nonneg
attribute [grind ←] Int.ediv_nonneg
attribute [grind =] Int.ediv_self
attribute [grind] pow_eq_zero
attribute [grind ←] Even.pow_nonneg
attribute [grind] even_iff_two_dvd
attribute [grind] Even.pow_pos_iff
attribute [grind ←] pow_nonneg pow_pos
attribute [grind ←] smul_nonneg
attribute [grind ←] abs_pos

attribute [grind] zero_le_one zero_lt_one zero_le_two zero_lt_two
attribute [grind] abs_nonneg Real.sqrt_nonneg
attribute [grind] Nat.cast_nonneg

attribute [grind] min_le_left min_le_right le_max_left le_max_right
attribute [grind] min_choice max_choice
attribute [grind =] min_eq_left min_eq_right max_eq_left max_eq_right

-- Canonical orders (these types are always non-negative)
attribute [grind] NNReal.coe_nonneg

-- Rational number structure
attribute [grind] Rat.den_pos

-- Type coercion preservation
attribute [grind] Nat.cast_nonneg
attribute [grind] NNReal.coe_nonneg

-- Extended reals
attribute [grind] EReal.coe_nonneg EReal.coe_pos

-- More fundamental positivity lemmas
attribute [grind ←] add_pos_of_pos_of_nonneg add_pos_of_nonneg_of_pos
attribute [grind ←] Real.sqrt_pos_of_pos

variable {ι α β E : Type*}

/- ## Numeric goals -/

example : 0 ≤ 0 := by grind

example : 0 ≤ 3 := by grind

example : 0 < 3 := by grind
example : (0 : EReal) < 2 := by grind
example : 0 < (2 : EReal) := by grind
example : (0 : EReal) < 2 := by grind

example : (0 : ℝ≥0∞) ≤ 1 := by grind
example : (0 : ℝ≥0∞) ≤ 0 := by grind
example : (0 : EReal) ≤ 0 := by grind
example : 0 ≤ (2 : EReal) := by grind

/- ## Goals working directly from a hypothesis -/

section FromHypothesis

-- set_option trace.Meta.debug true
-- sudo set_option trace.Tactic.positivity true
example {a : ℤ} (ha : 0 < a) : 0 < a := by grind
example {a : ℤ} (ha : 0 < a) : 0 ≤ a := by grind
example {a : ℤ} (ha : 0 < a) : a ≠ 0 := by grind
example {a : ℤ} (ha : 0 ≤ a) : 0 ≤ a := by grind
example {a : ℤ} (ha : a ≠ 0) : a ≠ 0 := by grind
example {a : ℤ} (ha : a = 0) : 0 ≤ a := by grind

section

variable [Zero α] [PartialOrder α] {a : α}

example (ha : 0 < a) : 0 < a := by grind
example (ha : 0 < a) : 0 ≤ a := by grind
example (ha : 0 < a) : a ≠ 0 := by grind
example (ha : 0 ≤ a) : 0 ≤ a := by grind
example (ha : a ≠ 0) : a ≠ 0 := by grind
example (ha : a = 0) : 0 ≤ a := by grind

end

/- ### Reversing hypotheses -/

example {a : ℤ} (ha : a > 0) : 0 < a := by grind
example {a : ℤ} (ha : a > 0) : 0 ≤ a := by grind
example {a : ℤ} (ha : a > 0) : a ≥ 0 := by grind
example {a : ℤ} (ha : a > 0) : a ≠ 0 := by grind
example {a : ℤ} (ha : a ≥ 0) : 0 ≤ a := by grind
example {a : ℤ} (ha : 0 ≠ a) : a ≠ 0 := by grind
example {a : ℤ} (ha : 0 < a) : a > 0 := by grind
example {a : ℤ} (ha : 0 < a) : a ≥ 0 := by grind
example {a : ℤ} (ha : 0 < a) : 0 ≠ a := by grind
example {a : ℤ} (ha : 0 ≤ a) : a ≥ 0 := by grind
example {a : ℤ} (ha : a ≠ 0) : 0 ≠ a := by grind
example {a : ℤ} (ha : a = 0) : a ≥ 0 := by grind
example {a : ℤ} (ha : 0 = a) : 0 ≤ a := by grind
example {a : ℤ} (ha : 0 = a) : a ≥ 0 := by grind

end FromHypothesis

/- ### Calling `norm_num` -/

example {a : ℤ} (ha : 3 = a) : 0 ≤ a := by grind
example {a : ℤ} (ha : 3 = a) : a ≠ 0 := by grind
example {a : ℤ} (ha : 3 = a) : 0 < a := by grind
example {a : ℤ} (ha : a = -1) : a ≠ 0 := by grind

example {a : ℤ} (ha : 3 ≤ a) : 0 ≤ a := by grind
example {a : ℤ} (ha : 3 ≤ a) : a ≠ 0 := by grind
example {a : ℤ} (ha : 3 ≤ a) : 0 < a := by grind

example {a : ℤ} (ha : 3 < a) : 0 ≤ a := by grind
example {a : ℤ} (ha : 3 < a) : a ≠ 0 := by grind
example {a : ℤ} (ha : 3 < a) : 0 < a := by grind

example {a b : ℤ} (h : 0 ≤ a + b) : 0 ≤ a + b := by grind

example {a : ℤ} (hlt : 0 ≤ a) (hne : a ≠ 0) : 0 < a := by grind

section

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

example : (1/4 - 2/3 : ℚ) ≠ 0 := by grind
example : (1/4 - 2/3 : α) ≠ 0 := by grind

end

/-
## Test for meta-variable instantiation

Reported on
https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F-tactics/topic/New.20tactic.3A.20.60positivity.60/near/300639970
-/

example : 0 ≤ 0 := by apply le_trans _ (le_refl _); grind


/- ## Tests of the @[positivity] plugin tactics (addition, multiplication, division) -/

-- example [Nonempty ι] [Zero α] {a : α} (ha : a ≠ 0) : const ι a ≠ 0 := by positivity
-- example [Zero α] [PartialOrder α] {a : α} (ha : 0 < a) : 0 ≤ const ι a := by positivity
-- example [Zero α] [PartialOrder α] {a : α} (ha : 0 ≤ a) : 0 ≤ const ι a := by positivity
-- example [Nonempty ι] [Zero α] [PartialOrder α] {a : α} (ha : 0 < a) : 0 < const ι a := by
--  positivity

section ite
variable {p : Prop} [Decidable p] {a b : ℤ}

example (ha : 0 < a) (hb : 0 < b) : 0 < ite p a b := by grind
example (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ ite p a b := by grind
example (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ ite p a b := by grind
example (ha : 0 < a) (hb : b ≠ 0) : ite p a b ≠ 0 := by grind
example (ha : a ≠ 0) (hb : 0 < b) : ite p a b ≠ 0 := by grind
example (ha : a ≠ 0) (hb : b ≠ 0) : ite p a b ≠ 0 := by grind

end ite

section MinMax

attribute [grind] lt_min_iff le_min_iff lt_max_iff le_max_iff min_lt_iff min_le_iff max_lt_iff max_le_iff

example {a b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < min a b := by grind
example {a b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ min a b := by grind
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ min a b := by grind
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ min a b := by grind
example {a b : ℚ} (ha : 0 < a) (hb : b ≠ 0) : min a b ≠ 0 := by grind
example {a b : ℚ} (ha : a ≠ 0) (hb : 0 < b) : min a b ≠ 0 := by grind
example {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : min a b ≠ 0 := by grind

example {a b : ℚ} (ha : 0 < a) : 0 < max a b := by grind
example {a b : ℚ} (hb : 0 < b) : 0 < max a b := by grind
example {a b : ℚ} (ha : 0 ≤ a) : 0 ≤ max a b := by grind
example {a b : ℚ} (hb : 0 ≤ b) : 0 ≤ max a b := by grind
example {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : max a b ≠ 0 := by grind

example : 0 ≤ max 3 4 := by grind
example : 0 ≤ max (0 : ℤ) (-3) := by grind
example : 0 ≤ max (-3 : ℤ) 5 := by grind

end MinMax

example {a b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by grind
example {a b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a * b := by grind
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a * b := by grind
example {a b : ℚ} (ha : 0 < a) (hb : b ≠ 0) : a * b ≠ 0 := by grind
example {a b : ℚ} (ha : a ≠ 0) (hb : 0 < b) : a * b ≠ 0 := by grind
example {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by grind

example {a b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by grind
example {a b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b := by grind
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by grind
example {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by grind
example {a b : ℚ} (ha : 0 < a) (hb : b ≠ 0) : a / b ≠ 0 := by grind
example {a b : ℚ} (ha : a ≠ 0) (hb : 0 < b) : a / b ≠ 0 := by grind
example {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 := by grind

example {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ a / b := by grind
example {a : ℤ} (ha : 0 < a) : 0 < a / a := by grind
example {a b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b := by grind
example {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by grind
example {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by grind

example {a : ℚ} (ha : 0 < a) : 0 < a⁻¹ := by grind
example {a : ℚ} (ha : 0 ≤ a) : 0 ≤ a⁻¹ := by grind
example {a : ℚ} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by grind

example {a : ℚ} (n : ℕ) (ha : 0 < a) : 0 < a ^ n := by grind
example {a : ℚ} (n : ℕ) (ha : 0 ≤ a) : 0 ≤ a ^ n := by grind
example {a : ℚ} (n : ℕ) (ha : a ≠ 0) : a ^ n ≠ 0 := by grind
example {a : ℚ} : 0 ≤ a ^ 18 := by grind
example {a : ℚ} (ha : a ≠ 0) : 0 < a ^ 18 := by grind

example {a : ℚ} (ha : 0 < a) : 0 < |a| := by grind
example {a : ℚ} (ha : a ≠ 0) : 0 < |a| := by grind
example (a : ℚ) : 0 ≤ |a| := by grind

-- Additional attributes for failing examples below
attribute [grind] smul_eq_zero smul_ne_zero

-- Scalar multiplication positivity
attribute [grind ←] smul_pos
attribute [grind ←] zsmul_pos
attribute [grind ←] zsmul_nonneg

example {a : ℤ} {b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < a • b := by grind
example {a : ℤ} {b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a • b := by grind
example {a : ℤ} {b : ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a • b := by grind
example {a : ℤ} {b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a • b := by grind
example {a : ℤ} {b : ℚ} (ha : 0 < a) (hb : b ≠ 0) : a • b ≠ 0 := by grind
example {a : ℤ} {b : ℚ} (ha : a ≠ 0) (hb : 0 < b) : a • b ≠ 0 := by grind
example {a : ℤ} {b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : a • b ≠ 0 := by grind

-- Test that the positivity extension for `a • b` can handle universe polymorphism.
example {R M : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Semiring M] [PartialOrder M] [IsStrictOrderedRing M]
    [SMulWithZero R M] [OrderedSMul R M] {a : R} {b : M} (ha : 0 < a) (hb : 0 < b) :
    0 < a • b := by grind

example {a : ℤ} (ha : 3 < a) : 0 ≤ a + a := by grind

example {a b : ℤ} (ha : 3 < a) (hb : 4 ≤ b) : 0 ≤ 3 + a + b + b + 14 := by grind

example {H : Type*} [AddCommGroup H] [LinearOrder H] [IsOrderedAddMonoid H]
    {a b : H} (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ a + a + b := by
  grind

example {a : ℤ} (ha : 3 < a) : 0 < a + a := by grind

example {a b : ℚ} (ha : 3 < a) (hb : 4 ≤ b) : 0 < 3 + a * b / 7 + b + 7 + 14 := by grind

example {a b : ℤ} (ha : 3 < a) (hb : 4 ≤ b) : 0 < 3 + a * b / 7 + b + 7 + 14 := by grind

section
variable {q : ℚ}

attribute [grind] Rat.num_ne_zero Rat.num_nonneg Rat.num_pos

example (hq : q ≠ 0) : q.num ≠ 0 := by grind
example : 0 < q.den := by grind
example (hq : 0 < q) : 0 < q := by grind
example (hq : 0 ≤ q) : 0 ≤ q.num := by grind

end


section ENNReal

variable {a b : ℝ≥0∞}

example : (0 : ℝ≥0∞) < 1 := by grind
example : (0 : ℝ≥0∞) < 2 := by grind

example : 0 ≤ a := by grind
example (ha : a ≠ 0) : 0 < a := by grind
example : 0 ≤ a + b := by grind
example (ha : a ≠ 0) : 0 < a + b := by grind
example : 0 < a + 5 := by grind
example : 0 < 2 * a + 3 := by grind
example (ha : 0 < a) : 0 < a + b := by grind

example : 0 ≤ a * b := by grind
example (ha : a ≠ 0) : 0 < 2 * a := by grind
example (ha : a ≠ 0) : 0 < a * 37 := by grind
example (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a * b := by grind
example (ha : a ≠ 0) : 0 ≤ a * b := by grind

end ENNReal

section EReal

variable {a b : EReal}

example (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by grind
example (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b := by grind
example (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b := by grind
example (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by grind
example (ha : 0 ≤ a) : 0 ≤ 2 + a := by grind
example (ha : 0 < a) : 0 < a + 2 := by grind

example (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by grind
example (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a * b := by grind
example (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a * b := by grind
example (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by grind
example (ha : 0 ≤ a) : 0 ≤ 2 * a := by grind
example (ha : 0 < a) : 0 < a * 2 := by grind

example : 0 < (5 : EReal) := by grind
example (_ha : 0 ≤ a) : 0 < a + 5 := by grind
example (_ha : 0 ≤ a) : 0 < 2 * a + 3 := by grind

end EReal

/-! ### Powers -/

section Powers

example [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]
    (a : α) : 0 < a ^ 0 := by positivity
example [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (a : α) : 0 ≤ a ^ 18 := by positivity
example [Semiring α] [PartialOrder α] [IsOrderedRing α]
    {a : α} {n : ℕ} (ha : 0 ≤ a) : 0 ≤ a ^ n := by positivity
example [Semiring α] [PartialOrder α] [IsStrictOrderedRing α]
    {a : α} {n : ℕ} (ha : 0 < a) : 0 < a ^ n := by positivity

example [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    (a : α) : 0 < a ^ (0 : ℤ) := by positivity
example [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (a : α) : 0 ≤ a ^ (18 : ℤ) := by positivity
example [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (a : α) : 0 ≤ a ^ (-34 : ℤ) := by positivity
example [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    {a : α} {n : ℤ} (ha : 0 ≤ a) : 0 ≤ a ^ n := by positivity
example [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    {a : α} {n : ℤ} (ha : 0 < a) : 0 < a ^ n := by positivity

-- example {a b : Cardinal.{u}} (ha : 0 < a) : 0 < a ^ b := by positivity
-- example {a b : Ordinal.{u}} (ha : 0 < a) : 0 < a ^ b := by positivity

example {a b : ℝ} (ha : 0 ≤ a) : 0 ≤ a ^ b := by positivity
example {a b : ℝ} (ha : 0 < a) : 0 < a ^ b := by positivity
example {a : ℝ≥0} {b : ℝ} (ha : 0 < a) : 0 < (a : ℝ) ^ b := by positivity
-- example {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a ^ b := by positivity
-- example {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ b := by positivity
example {a : ℝ} : 0 < a ^ 0 := by positivity

example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 2 + a := by positivity
example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by positivity
example {a : ℤ} (ha : 3 < a) : 0 < a ^ 2 + a := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : b ≥ 4) : 0 ≤ 3 * a ^ 2 * b + b * 7 + 14 := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : b ≥ 4) : 0 < 3 * a ^ 2 * b + b * 7 + 14 := by positivity

example {a b : ℤ} (ha : 3 < a) : 0 ≤ min a (b ^ 2) := by positivity
example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by positivity
example {b : ℤ} : 0 ≤ max (b ^ 2) 0 := by positivity

end Powers

section FloorCeil

example {a : ℝ} (ha : 0 < a) : 0 ≤ ⌊a⌋ := by positivity
example {a : ℝ} (ha : 0 ≤ a) : 0 ≤ ⌊a⌋ := by positivity

example {a : ℝ} (ha : 0 < a) : 0 < ⌈a⌉₊ := by positivity
example {a : ℝ} (ha : 0 < a) : 0 < ⌈a⌉ := by positivity
example {a : ℝ} (ha : 0 ≤ a) : 0 ≤ ⌈a⌉ := by positivity

end FloorCeil

section Abs

example {a : ℤ} : 0 ≤ |a| := by positivity

example {a : ℤ} : 0 < |a| + 3 := by positivity

example {n : ℤ} (hn : 0 < n) : 0 < n.natAbs := by positivity
example {n : ℤ} (hn : n ≠ 0) : 0 < n.natAbs := by positivity
example {n : ℤ} : 0 ≤ n.natAbs := by positivity

example {a : ℤ} (ha : 1 < a) : 0 < |(3:ℤ) + a| := by positivity

example (a : ℤ) : 0 ≤ a⁺ := by positivity
example (a : ℤ) (ha : 0 < a) : 0 < a⁺ := by positivity
example (a : ℤ) : 0 ≤ a⁻ := by positivity

end Abs

-- -- test that the tactic can ignore arithmetic operations whose associated extension tactic
-- -- requires more typeclass assumptions than are available
example {R : Type*} [Zero R] [Div R] [LinearOrder R] {a b c : R} (_h1 : 0 < a) (_h2 : 0 < b)
  (h3 : 0 < c) :
  0 < max (a / b) c := by positivity

example
    [Semiring α] [PartialOrder α] [IsOrderedRing α]
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] [SMulWithZero α β]
    [OrderedSMul α β] {a : α} (ha : 0 < a) {b : β} (hb : 0 < b) : 0 ≤ a • b := by
  positivity

example (n : ℕ) : 0 < n.succ := by positivity
example (n : ℕ+) : 0 < (↑n : ℕ) := by positivity
example (n : ℕ) : 0 < n ! := by positivity
example (n k : ℕ) : 0 < (n+1).ascFactorial k := by positivity

example {α : Type*} (s : Finset α) (hs : s.Nonempty) : 0 < #s := by positivity
example {α : Type*} [Fintype α] [Nonempty α] : 0 < Fintype.card α := by positivity

section Norms

example [SeminormedGroup E] {a : E} (_ha : a ≠ 1) : 0 ≤ ‖a‖ := by positivity
example [NormedGroup E] {a : E} : 0 ≤ ‖a‖ := by positivity
example [NormedGroup E] {a : E} (ha : a ≠ 1) : 0 < ‖a‖ := by positivity

example [SeminormedAddGroup E] {a : E} (_ha : a ≠ 0) : 0 ≤ ‖a‖ := by positivity
example [NormedAddGroup E] {a : E} : 0 ≤ ‖a‖ := by positivity
example [NormedAddGroup E] {a : E} (ha : a ≠ 0) : 0 < ‖a‖ := by positivity

example [MetricSpace α] (x y : α) : 0 ≤ dist x y := by positivity
example [MetricSpace α] {s : Set α} : 0 ≤ Metric.diam s := by positivity

example {E : Type*} [AddGroup E] {p : AddGroupSeminorm E} {x : E} : 0 ≤ p x := by positivity
example {E : Type*} [Group E] {p : GroupSeminorm E} {x : E} : 0 ≤ p x := by positivity

end Norms

-- example {r : α → β → Prop} [∀ a, DecidablePred (r a)] {s : Finset α} {t : Finset β} :
--   0 ≤ Rel.edgeDensity r s t := by positivity
-- example {G : SimpleGraph α} [DecidableRel G.adj] {s t : finset α} :
--   0 ≤ G.edgeDensity s t := by positivity

/-! ### Special functions -/

section SpecialFunctions

example {r : ℝ} : 0 < Real.exp r := by positivity

example {n : ℕ} : 0 ≤ Real.log n := by positivity
example {n : ℤ} : 0 ≤ Real.log n := by positivity
example : 0 < Real.log 2 := by positivity
example : 0 < Real.log 1.01 := by positivity
example : 0 ≠ Real.log 0.99 := by positivity
example : 0 < Real.log (-2) := by positivity
example : 0 < Real.log (-1.01) := by positivity
example : 0 ≠ Real.log (-0.99) := by positivity
example : 0 ≤ Real.log 1 := by positivity
example : 0 ≤ Real.log 0 := by positivity
example : 0 ≤ Real.log (-1) := by positivity

end SpecialFunctions

/-! ### `sqrt` on `ℝ` and `ℝ≥0` -/

section Sqrt

attribute [grind ←] NNReal.sqrt_pos_of_pos

example : 0 < NNReal.sqrt 5 := by grind
example : 0 ≤ Real.sqrt (-5) := by grind
example (x : ℝ) : 0 ≤ Real.sqrt x := by grind
example : 0 < Real.sqrt 5 := by grind

example {a : ℝ} (_ha : 0 ≤ a) : 0 ≤ Real.sqrt a := by grind

example {a : ℝ} (ha : 0 ≤ a) : 0 < Real.sqrt (a + 3) := by grind

end Sqrt

/- ### Canonical orders -/

example {a : ℕ} : 0 ≤ a := by grind
example {a : ℚ≥0} : 0 ≤ a := by grind
example {a : ℝ≥0} : 0 ≤ a := by grind
example {a : ℝ≥0∞} : 0 ≤ a := by grind

/- ### Coercions -/

section Coercions

example {a : ℕ} : (0 : ℤ) ≤ a := by grind
example {a : ℕ} : (0 : ℚ) ≤ a := by grind
example {a : ℕ} : (0 : EReal) ≤ a := by grind
example {a : ℕ} (ha : 0 < a) : (0 : ℤ) < a := by grind
example {a : ℕ} (ha : 0 < a) : (0 : ℚ) < a := by grind
example {a : ℕ} (ha : 0 < a) : (0 : EReal) < a := by grind
example {a : ℤ} (ha : a ≠ 0) : (a : ℚ) ≠ 0 := by grind
example {a : ℤ} (ha : 0 ≤ a) : (0 : ℚ) ≤ a := by grind
example {a : ℤ} (ha : 0 < a) : (0 : ℚ) < a := by grind
example {a : ℚ} (ha : a ≠ 0) : (a : ℝ) ≠ 0 := by grind
example {a : ℚ} (ha : 0 ≤ a) : (0 : ℝ) ≤ a := by grind
example {a : ℚ} (ha : 0 < a) : (0 : ℝ) < a := by grind
example {a : ℚ≥0} (ha : a ≠ 0) : (a : ℝ≥0) ≠ 0 := by grind
example {a : ℚ≥0} : (0 : ℝ≥0) ≤ a := by grind
example {a : ℚ≥0} (ha : 0 < a) : (0 : ℝ≥0) < a := by grind
example {r : ℝ≥0} : (0 : ℝ) ≤ r := by grind
example {r : ℝ≥0} (hr : 0 < r) : (0 : ℝ) < r := by grind

example : (0 : ℝ) < ↑(3 : ℝ≥0) := by grind

example {r : ℝ≥0} (hr : 0 < r) : (0 : ℝ≥0∞) < r := by grind
example {r : ℝ≥0} : (0 : EReal) ≤ r := by grind -- TODO: Handle `coe_trans`
example {r : ℝ≥0} (hr : 0 < r) : (0 : EReal) < r := by grind
example {r : ℝ} (hr : 0 ≤ r) : (0 : EReal) ≤ r := by grind
example {r : ℝ} (hr : 0 < r) : (0 : EReal) < r := by grind
-- example {r : ℝ} (hr : 0 ≤ r) : (0 : Hyperreal) ≤ r := by grind
-- example {r : ℝ} (hr : 0 < r) : (0 : Hyperreal) < r := by grind
example {r : ℝ≥0∞} : (0 : EReal) ≤ r := by grind
example {r : ℝ≥0∞} (hr : 0 < r) : (0 : EReal) < r := by grind

-- example {α : Type*} [OrderedRing α] {n : ℤ} : 0 ≤ ((n ^ 2 : ℤ) : α) := by grind
example {r : ℝ≥0} : 0 ≤ ((r : ℝ) : EReal) := by grind
example {r : ℝ≥0} : 0 < ((r + 1 : ℝ) : EReal) := by grind

end Coercions

/- ## Integrals -/

section Integral

open MeasureTheory

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace D] [BorelSpace D]
  (μ : Measure D)

example (f : D → E) : 0 ≤ ∫ x, ‖f x‖ ∂μ := by grind
example (f g : D → E) : 0 ≤ ∫ x, ‖f x‖ + ‖g x‖ ∂μ := by grind
example (f : D → E) (c : ℝ) (hc : 0 < c): 0 ≤ ∫ x, c * ‖f x‖ ∂μ := by grind

end Integral

/-! ## Infinite Sums -/

example (f : ℕ → ℝ) : 0 ≤ ∑' n, f n ^ 2 := by grind
example (f : ℕ → ℝ≥0) (c : ℝ) (hc : 0 < c) : 0 ≤ ∑' n, c * f n := by grind
example [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    [TopologicalSpace α] [OrderClosedTopology α] (f : ℚ → α) :
    0 ≤ ∑' q, (f q)^2 := by
  grind

-- Make sure that the extension doesn't produce an invalid term by accidentally unifying `?n` with
-- `0` because of the `hf` assumption
set_option linter.unusedVariables false in
example (f : ℕ → ℕ) (hf : 0 ≤ f 0) : 0 ≤ ∑' n, f n := by grind

/-! ## Big operators -/

section BigOperators

example (n : ℕ) (f : ℕ → ℤ) : 0 ≤ ∑ j ∈ range n, f j ^ 2 := by grind
example (f : ULift.{2} ℕ → ℤ) (s : Finset (ULift.{2} ℕ)) : 0 ≤ ∑ j ∈ s, f j ^ 2 := by grind
example (n : ℕ) (f : ℕ → ℤ) : 0 ≤ ∑ j : Fin 8, ∑ i ∈ range n, (f j ^ 2 + i ^ 2) := by grind
example (n : ℕ) (f : ℕ → ℤ) : 0 < ∑ j : Fin (n + 1), (f j ^ 2 + 1) := by grind
example (f : Empty → ℤ) : 0 ≤ ∑ j : Empty, f j ^ 2 := by grind
example (f : ℕ → ℤ) : 0 < ∑ j ∈ ({1} : Finset ℕ), (f j ^ 2 + 1) := by
  have : Finset.Nonempty {1} := singleton_nonempty 1
  grind
example (s : Finset ℕ) : 0 ≤ ∑ j ∈ s, j := by grind
example (s : Finset ℕ) : 0 ≤ s.sum id := by grind
example (s : Finset ℕ) (f : ℕ → ℕ) (a : ℕ) : 0 ≤ s.sum (f a) := by grind

-- Make sure that the extension doesn't produce an invalid term by accidentally unifying `?n` with
-- `0` because of the `hf` assumption
set_option linter.unusedVariables false in
example (f : ℕ → ℕ) (hf : 0 ≤ f 0) : 0 ≤ ∑ n ∈ Finset.range 10, f n := by grind

set_option linter.unusedVariables false in
example (n : ℕ) : ∏ j ∈ range n, (-1) ≠ 0 := by grind
example (n : ℕ) (a : ℕ → ℤ) : 0 ≤ ∏ j ∈ range n, a j^2 := by grind
example (a : ULift.{2} ℕ → ℤ) (s : Finset (ULift.{2} ℕ)) : 0 ≤ ∏ j ∈ s, a j^2 := by grind
example (n : ℕ) (a : ℕ → ℤ) : 0 ≤ ∏ j : Fin 8, ∏ i ∈ range n, (a j^2 + i ^ 2) := by grind
example (n : ℕ) (a : ℕ → ℤ) : 0 < ∏ j : Fin (n + 1), (a j^2 + 1) := by grind
example (a : ℕ → ℤ) : 0 < ∏ j ∈ ({1} : Finset ℕ), (a j^2 + 1) := by
  have : Finset.Nonempty {1} := singleton_nonempty 1
  grind
example (s : Finset ℕ) : 0 ≤ ∏ j ∈ s, j := by grind
example (s : Finset ℕ) : 0 ≤ s.sum id := by grind
example (s : Finset ℕ) (f : ℕ → ℕ) (a : ℕ) : 0 ≤ s.sum (f a) := by grind

-- Make sure that the extension doesn't produce an invalid term by accidentally unifying `?n` with
-- `0` because of the `hf` assumption
set_option linter.unusedVariables false in
example (f : ℕ → ℕ) (hf : 0 ≤ f 0) : 0 ≤ ∏ n ∈ Finset.range 10, f n := by grind

-- Make sure that `positivity` isn't too greedy by trying to prove that a product is positive
-- because its body is even if multiplication isn't strictly monotone
example [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
    {a : α} (ha : 0 < a) : 0 ≤ ∏ _i ∈ {(0 : α)}, a := by grind

end BigOperators

/- ## Other extensions -/

example [Zero β] [PartialOrder β] [FunLike F α β] [NonnegHomClass F α β]
    (f : F) (x : α) : 0 ≤ f x := by grind

example [Semiring S] [PartialOrder S] [IsOrderedRing S] [Semiring R]
    (abv : R → S) [IsAbsoluteValue abv] (x : R) :
    0 ≤ abv x := by
  grind
