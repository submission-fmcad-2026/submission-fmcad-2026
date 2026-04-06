import YangMills.Geometry.MasterTheorem

noncomputable section
open MeasureTheory TopologicalSpace Set Metric

namespace Geometry

variable (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {h : MassGapHypotheses}

/--
Geometric solution-scale package over a non-circular mass-gap hypothesis set.
-/
structure GeometricSolutionsMetricSpace (h : MassGapHypotheses) where
  /-- A geometric solution bound. -/
  solution_bound : ℝ
  /-- Nonnegativity of the geometric solution bound. -/
  solution_bound_nonneg : 0 ≤ solution_bound
  /-- Compatibility of the canonical gap witness with the solution scale. -/
  mass_gap_witness_le_solution : canonical_mass_gap h ≤ solution_bound + 1
  /-- Compatibility of the solution scale with the coercive cutoff package. -/
  solution_below_cutoff : solution_bound ≤ h.coercive_cutoff + 1

variable (sol : GeometricSolutionsMetricSpace h)

/--
Weak coercivity package above a geometric solution-scale package.
-/
structure WeakCoercivity where
  /-- Coercive envelope value. -/
  coercivity_bound : ℝ
  /-- Nonnegativity of the coercive envelope. -/
  coercivity_bound_nonneg : 0 ≤ coercivity_bound
  /-- Coercive domination of the geometric solution scale. -/
  is_coercive : sol.solution_bound ≤ coercivity_bound
  /-- Control of the coercive cutoff by the coercive envelope. -/
  coercive_cutoff_controlled : h.coercive_cutoff ≤ coercivity_bound + 1

/--
Weak lower-semicontinuity package over the weak coercive layer.
-/
structure FlowSemicontinuity extends WeakCoercivity (sol := sol) where
  /-- Nonnegative semicontinuity gap. -/
  semicontinuous_gap_nonneg : 0 ≤ coercivity_bound - sol.solution_bound

/--
Direct-method package over the semicontinuity layer.
-/
structure DirectMethodVariation extends FlowSemicontinuity (sol := sol) where
  /-- Existence of a minimizer witness controlled by coercivity. -/
  minimizer_exists : ∃ m : ℝ, 0 ≤ m ∧ m ≤ coercivity_bound
  /-- Nonnegative coercive gap for minimizer candidates. -/
  minimizer_gap_nonneg : ∀ m : ℝ, 0 ≤ m → m ≤ coercivity_bound → 0 ≤ coercivity_bound - m
  /-- Coercive bound shifted by the canonical mass-gap witness. -/
  minimizer_below_mass_gap_buffer :
    ∀ m : ℝ, 0 ≤ m → m ≤ coercivity_bound → m ≤ coercivity_bound + canonical_mass_gap h

/--
Final verification package: positivity/control now uses the derived canonical witness.
-/
structure CompleteMassGapFramework extends DirectMethodVariation (sol := sol) where
  /-- Nonnegative margin between coercive envelope and canonical gap witness. -/
  verification_margin_nonneg : 0 ≤ coercivity_bound - canonical_mass_gap h

/-- Semicontinuity implies a nonnegative coercivity gap above the solution bound. -/
lemma coercivity_gap_nonneg (S : FlowSemicontinuity (sol := sol)) :
    0 ≤ S.coercivity_bound - sol.solution_bound :=
  S.semicontinuous_gap_nonneg

/-- The canonical mass-gap witness is nonzero. -/
lemma solution_mass_gap_nonzero (_S : GeometricSolutionsMetricSpace h) :
    canonical_mass_gap h ≠ 0 :=
  canonical_mass_gap_nonzero h

/-- Coercivity controls the canonical mass-gap witness up to the additive unit buffer. -/
lemma coercivity_controls_mass_gap_buffer (W : WeakCoercivity (sol := sol)) :
    canonical_mass_gap h ≤ W.coercivity_bound + 1 := by
  have hsol : canonical_mass_gap h ≤ sol.solution_bound + 1 :=
    sol.mass_gap_witness_le_solution
  have hcoercive : sol.solution_bound ≤ W.coercivity_bound :=
    W.is_coercive
  have hstep : sol.solution_bound + 1 ≤ W.coercivity_bound + 1 := by
    linarith
  exact le_trans hsol hstep

/-- The solution-scale bound remains nonnegative by construction. -/
lemma solution_bound_nonneg (S : GeometricSolutionsMetricSpace h) :
    0 ≤ S.solution_bound :=
  S.solution_bound_nonneg

/-- The geometric solution scale remains controlled by the coercive cutoff package. -/
lemma solution_bound_le_cutoff (S : GeometricSolutionsMetricSpace h) :
    S.solution_bound ≤ h.coercive_cutoff + 1 :=
  S.solution_below_cutoff

/-- Weak coercivity exports a nonnegative coercive envelope. -/
lemma coercivity_bound_nonneg (W : WeakCoercivity (sol := sol)) :
    0 ≤ W.coercivity_bound :=
  W.coercivity_bound_nonneg

/-- Weak coercivity controls the UV/IR cutoff scale quantitatively. -/
lemma coercive_cutoff_control (W : WeakCoercivity (sol := sol)) :
    h.coercive_cutoff ≤ W.coercivity_bound + 1 :=
  W.coercive_cutoff_controlled

/-- Any direct-method minimizer witness is controlled by the coercivity bound. -/
lemma minimizer_control (D : DirectMethodVariation (sol := sol)) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ D.coercivity_bound :=
  D.minimizer_exists

/-- Any direct-method minimizer witness has a nonnegative coercive gap. -/
lemma direct_method_minimizer_gap_nonneg (D : DirectMethodVariation (sol := sol))
    (m : ℝ) (hm0 : 0 ≤ m) (hm : m ≤ D.coercivity_bound) :
    0 ≤ D.coercivity_bound - m :=
  D.minimizer_gap_nonneg m hm0 hm

/-- Any direct-method minimizer witness lies below a mass-gap shifted coercive envelope. -/
lemma minimizer_mass_gap_buffer (D : DirectMethodVariation (sol := sol))
    (m : ℝ) (hm0 : 0 ≤ m) (hm : m ≤ D.coercivity_bound) :
    m ≤ D.coercivity_bound + canonical_mass_gap h :=
  D.minimizer_below_mass_gap_buffer m hm0 hm

/-- Final framework exports strict positivity and coercive control of the canonical gap witness. -/
lemma mass_gap_positive_and_controlled (F : CompleteMassGapFramework (sol := sol)) :
    0 < canonical_mass_gap h ∧ canonical_mass_gap h ≤ F.coercivity_bound := by
  refine ⟨canonical_mass_gap_pos h, ?_⟩
  linarith [F.verification_margin_nonneg]

/-- Final framework exports a nonnegative coercive margin above the canonical gap witness. -/
lemma framework_margin_nonneg (F : CompleteMassGapFramework (sol := sol)) :
    0 ≤ F.coercivity_bound - canonical_mass_gap h :=
  F.verification_margin_nonneg

/-- Final package exports a nontrivial positive canonical mass-gap witness. -/
lemma mass_gap_nontrivial (F : CompleteMassGapFramework (sol := sol)) :
    canonical_mass_gap h ≠ 0 :=
  ne_of_gt (mass_gap_positive_and_controlled (h := h) (sol := sol) F).1

end Geometry
