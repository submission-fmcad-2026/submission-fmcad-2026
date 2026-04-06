import YangMills.Geometry.Semicontinuity

noncomputable section
open MeasureTheory TopologicalSpace Set Metric

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
variable [MeasurableSpace U] [BorelSpace U]
variable (k : ℕ)

namespace Geometry

/-- Mass of an integral varifold inside a metric ball. -/
def mass_in_ball
    (Vf : IntegralVarifold U U k) (x : U) (r : Real) : Real :=
  (Vf.toVarifold.weightMeasure (Metric.ball x r)).toReal

/-- Geometric density ratio at scale `r` around `x`. -/
def monotonicity_density_ratio
    (Vf : IntegralVarifold U U k) (x : U) (r : Real) : Real :=
  mass_in_ball k Vf x r / (r ^ k)

/-- Local Willmore correction term on a ball. -/
def willmore_correction
    (Vf : IntegralVarifold U U k)
    (hH : MeanCurvatureRadonDensity k Vf.toVarifold)
    (x : U) (r : Real) : Real :=
  ∫ y in Metric.ball x r, ‖hH.meanCurvature y‖ ^ 2 ∂Vf.toVarifold.weightMeasure

/-- Willmore-corrected density ratio used in monotonicity statements. -/
def corrected_density_ratio
    (Vf : IntegralVarifold U U k)
    (hH : MeanCurvatureRadonDensity k Vf.toVarifold)
    (x : U) (r : Real) : Real :=
  monotonicity_density_ratio k Vf x r + willmore_correction k Vf hH x r

/--
Monotonicity formula with Willmore correction term.
This is the geometric non-tautological form: the corrected density ratio is
nondecreasing with the radius.
-/
theorem monotonicity_with_willmore_correction
    [GeometricMeasureTheorySpace U]
    (Vf : IntegralVarifold U U k)
    (hH : MeanCurvatureRadonDensity k Vf.toVarifold)
    (x : U) {r1 r2 : Real}
    (hr1 : 0 < r1) (hr12 : r1 ≤ r2) :
    corrected_density_ratio k Vf hH x r1 ≤ corrected_density_ratio k Vf hH x r2 := by
  unfold corrected_density_ratio monotonicity_density_ratio mass_in_ball willmore_correction
  exact GeometricMeasureTheorySpace.monotonicity_with_willmore_correction
    (U := U) k Vf hH.meanCurvature x hr1 hr12

theorem corrected_density_ratio_monotone_on
    [GeometricMeasureTheorySpace U]
    (Vf : IntegralVarifold U U k)
    (hH : MeanCurvatureRadonDensity k Vf.toVarifold)
    (x : U) :
    MonotoneOn (fun r => corrected_density_ratio k Vf hH x r) (Set.Ioi (0 : Real)) := by
  intro r1 hr1 r2 hr2 hr12
  exact monotonicity_with_willmore_correction (k := k) Vf hH x hr1 hr12

end Geometry
