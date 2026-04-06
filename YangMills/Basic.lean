import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Yang-Mills Basic Definitions

This file contains basic definitions and utilities shared across the formalization.
-/


noncomputable section

/-! ## Section 1: Basic Constants -/

/-- The spacetime dimension (4 for Yang-Mills in ℝ⁴). -/
def spacetimeDim : ℕ := 4

/-- The surface dimension (2 for worldsheets). -/
def surfaceDim : ℕ := 2

/-! ## Section 2: Euclidean Space Abbreviations -/

/-- Euclidean 4-space ℝ⁴. -/
abbrev R4 := EuclideanSpace ℝ (Fin 4)

/-- Euclidean 2-space ℝ². -/
abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-! ## Section 3: Lattice Definitions (Preview for Discretization) -/

/-- Points on the integer lattice εℤ⁴. -/
def isLatticePoint (ε : ℝ) (v : R4) : Prop :=
  ∀ i : Fin 4, ∃ n : ℤ, v i = ε * n

/-- The unit hypercube [0,1]⁴. -/
def unitHypercube : Set R4 :=
  { v | ∀ i : Fin 4, 0 ≤ v i ∧ v i ≤ 1 }

/-- A scaled hypercube [0,ε]⁴. -/
def scaledHypercube (ε : ℝ) : Set R4 :=
  { v | ∀ i : Fin 4, 0 ≤ v i ∧ v i ≤ ε }

/-! ## Section 4: Flat Norm Utilities -/

/-- Core flat-norm model built from mass and boundary mass. -/
def flatNormBasic (mass : ℝ) (boundaryMass : ℝ) : ℝ := mass + boundaryMass

/-- Flat norm is non-negative when masses are non-negative. -/
lemma flatNormBasic_nonneg {m b : ℝ} (hm : 0 ≤ m) (hb : 0 ≤ b) : 
    0 ≤ flatNormBasic m b := by
  simp only [flatNormBasic]
  linarith

/-- Triangle inequality for basic flat norm. -/
lemma flatNormBasic_triangle (m1 b1 m2 b2 : ℝ) :
    flatNormBasic (m1 + m2) (b1 + b2) = flatNormBasic m1 b1 + flatNormBasic m2 b2 := by
  simp only [flatNormBasic]
  ring

/-- Monotonicity in the mass component. -/
lemma flatNormBasic_mono_left {m1 m2 b : ℝ} (hm : m1 ≤ m2) :
    flatNormBasic m1 b ≤ flatNormBasic m2 b := by
  simp [flatNormBasic]
  linarith

/-- Monotonicity in the boundary-mass component. -/
lemma flatNormBasic_mono_right {m b1 b2 : ℝ} (hb : b1 ≤ b2) :
    flatNormBasic m b1 ≤ flatNormBasic m b2 := by
  simp [flatNormBasic]
  linarith

/-- Vanishing of the flat norm with nonnegative components forces both masses to vanish. -/
lemma flatNormBasic_eq_zero_of_nonneg {m b : ℝ}
    (hm : 0 ≤ m) (hb : 0 ≤ b) (h0 : flatNormBasic m b = 0) :
    m = 0 ∧ b = 0 := by
  have h0' : m + b = 0 := by
    simpa [flatNormBasic] using h0
  have hm0 : m ≤ 0 := by
    linarith [h0', hb]
  have hb0 : b ≤ 0 := by
    linarith [h0', hm]
  exact ⟨le_antisymm hm0 hm, le_antisymm hb0 hb⟩

end

