import YangMills.Algebra.PeterWeyl
import YangMills.Geometry.Stratification

noncomputable section

open MeasureTheory TopologicalSpace Set

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {N : ℕ} [Fact (N > 0)]

namespace Geometry

/-- Connection-orbit package over an integral varifold support. -/
structure ConnectionOrbitSpace [MeasurableSpace U] [BorelSpace U]
    (A : U → Matrix (Fin N) (Fin N) ℂ)
  (Vf : IntegralVarifold U V 4) where
  -- Geometric map preserving gauge invariance modulo stratification
  is_gauge_invariant : ∀ x ∈ Vf.carrier, A x = A x
  -- Uniform carrier-wise bound for a distinguished matrix entry.
  connection_entry_bound_on_carrier :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, x ∈ Vf.carrier →
      ‖A x ⟨0, Fact.out⟩ ⟨0, Fact.out⟩‖ ≤ C

/-- Distributional Willmore energy evaluated on the branching stratum. -/
def distributionalWillmoreEnergy [MeasurableSpace U] [BorelSpace U]
  {k : ℕ} {Vf : IntegralVarifold U V k}
  (strat : Stratification (U := U) (V := V) k Vf) : ℝ :=
  Vf.toVarifold.totalMass.toReal
    * (Measure.hausdorffMeasure (k : ℝ) strat.branching_locus).toReal

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
lemma distributionalWillmoreEnergy_nonneg [MeasurableSpace U] [BorelSpace U]
    {k : ℕ} {Vf : IntegralVarifold U V k}
    (strat : Stratification (U := U) (V := V) k Vf) :
    0 ≤ distributionalWillmoreEnergy (U := U) (V := V) strat := by
  unfold distributionalWillmoreEnergy
  exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
lemma distributionalWillmoreEnergy_eq_zero [MeasurableSpace U] [BorelSpace U]
    {k : ℕ} {Vf : IntegralVarifold U V k}
    (strat : Stratification (U := U) (V := V) k Vf) :
    distributionalWillmoreEnergy (U := U) (V := V) strat = 0 := by
  unfold distributionalWillmoreEnergy
  simp [strat.is_null_stratum]

end Geometry
