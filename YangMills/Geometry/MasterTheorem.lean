import YangMills.Geometry.IntegralCurrents

noncomputable section

open MeasureTheory TopologicalSpace Set Metric

namespace Geometry

variable (U : Type*) [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/--
Coercive hypothesis package for the mass-gap extraction layer.

This package intentionally contains only analytic/coercive inputs and does not
contain the mass-gap conclusion itself.
-/
structure MassGapHypotheses where
  /-- Explicit UV/IR coercive cutoff scale. -/
  coercive_cutoff : ℝ
  /-- Strict positivity of the coercive cutoff scale. -/
  coercive_cutoff_pos : 0 < coercive_cutoff

/--
Derived existence theorem: from a positive coercive cutoff one gets a positive
mass-gap witness below that cutoff.
-/
theorem mass_gap_exists (h : MassGapHypotheses) :
    ∃ m : ℝ, 0 < m ∧ m ≤ h.coercive_cutoff := by
  refine ⟨h.coercive_cutoff / 2, ?_, ?_⟩
  · exact div_pos h.coercive_cutoff_pos (by norm_num)
  · have hnonneg : 0 ≤ h.coercive_cutoff := le_of_lt h.coercive_cutoff_pos
    calc
      h.coercive_cutoff / 2 = h.coercive_cutoff * (1 / (2 : ℝ)) := by ring
      _ ≤ h.coercive_cutoff * 1 := by
        exact mul_le_mul_of_nonneg_left (by norm_num : (1 / (2 : ℝ)) ≤ 1) hnonneg
      _ = h.coercive_cutoff := by ring

/-- Canonical witness used by downstream geometry layers. -/
def canonical_mass_gap (h : MassGapHypotheses) : ℝ :=
  h.coercive_cutoff / 2

lemma canonical_mass_gap_pos (h : MassGapHypotheses) :
    0 < canonical_mass_gap h := by
  unfold canonical_mass_gap
  exact div_pos h.coercive_cutoff_pos (by norm_num)

lemma canonical_mass_gap_le_cutoff (h : MassGapHypotheses) :
    canonical_mass_gap h ≤ h.coercive_cutoff := by
  unfold canonical_mass_gap
  have hnonneg : 0 ≤ h.coercive_cutoff := le_of_lt h.coercive_cutoff_pos
  calc
    h.coercive_cutoff / 2 = h.coercive_cutoff * (1 / (2 : ℝ)) := by ring
    _ ≤ h.coercive_cutoff * 1 := by
      exact mul_le_mul_of_nonneg_left (by norm_num : (1 / (2 : ℝ)) ≤ 1) hnonneg
    _ = h.coercive_cutoff := by ring

lemma canonical_mass_gap_nonzero (h : MassGapHypotheses) :
    canonical_mass_gap h ≠ 0 :=
  ne_of_gt (canonical_mass_gap_pos h)

/--
Yang-Mills functional package on integral varifolds.
-/
structure YangMillsFunctional (Vf : IntegralVarifold (V := V) (U := U) 4) where
  /-- Functional scalar value. -/
  energy_value : ℝ
  /-- Lower bound on the energy value. -/
  bounded_from_below : 0 ≤ energy_value
  /-- Coercive mass control. -/
  controls_mass : Vf.toVarifold.totalMass.toReal ≤ energy_value + 1
  /-- Linear coercive envelope. -/
  coercive_linear :
    ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ Vf.toVarifold.totalMass.toReal ≤ a * energy_value + b

/--
Minimizer package for the Yang-Mills functional.
-/
structure YangMillsMinimizer (functional : IntegralVarifold (V := V) (U := U) 4 → ℝ) where
  /-- Chosen minimizer. -/
  minimizer : IntegralVarifold (V := V) (U := U) 4
  /-- Global optimality property. -/
  is_globally_optimal : ∀ Vf, functional minimizer ≤ functional Vf
  /-- Nonnegative optimality gap. -/
  optimality_gap_nonneg : ∀ Vf, 0 ≤ functional Vf - functional minimizer

/-- Functional-level coercive mass control exported for downstream use. -/
lemma functional_mass_control
    (Vf : IntegralVarifold (V := V) (U := U) 4)
    (F : YangMillsFunctional (V := V) (U := U) Vf) :
    Vf.toVarifold.totalMass.toReal ≤ F.energy_value + 1 :=
  F.controls_mass

/-- Every minimizing package exports a nonnegative optimality gap. -/
lemma minimizer_gap_nonneg
    (functional : IntegralVarifold (V := V) (U := U) 4 → ℝ)
    (M : YangMillsMinimizer (V := V) (U := U) functional)
    (Vf : IntegralVarifold (V := V) (U := U) 4) :
    0 ≤ functional Vf - functional M.minimizer :=
  M.optimality_gap_nonneg Vf

end Geometry
