/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/-! # Homework 1 -/


/- 5 points -/
theorem problem1 {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 := by
  calc
    p = p + 4 * q - 4 * (q - 1) - 4 := by ring
    _ = 1 - 4 * (2) - 4 := by rw [h1, h2]
    _ = -11 := by ring


/- 5 points -/
theorem problem2 {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by
  calc
    a = ((a + 2 * b) + 2 * (a - b))/3:= by ring
    _ = (4 + 2 * 1) / 3 := by rw [h1, h2]
    _ = 2 := by ring

/- 5 points -/
theorem problem3 {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x
    _ = x * (x * (x - 8) + 2) := by ring
    _ ≥ x * (x * (9 - 8) + 2) := by rel [hx]
    _ = x * (x + 2) := by ring
    _ ≥ 9 * (9 + 2) := by rel [hx]
    _ ≥ 99 := by numbers
    _ ≥ 3 := by numbers

/- 5 points -/
theorem problem4 {x : ℚ} : x ^ 2 - 2 * x ≥ -1 := by
  calc
    x ^ 2 - 2 * x
    _ = (x - 1) ^ 2 - 1 := by ring
    _ ≥ -1 := by extra

/- 5 points -/
theorem problem5 (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : b - a ≥ 0 := by addarith [h2]
  have h4 : b + a ≥ 0 := by addarith [h1]
  calc
    a ^ 2
    _ ≤ a ^ 2 + (b - a) * (b + a) := by extra
    _ = b ^ 2 := by ring
