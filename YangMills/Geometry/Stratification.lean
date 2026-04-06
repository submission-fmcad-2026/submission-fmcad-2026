import YangMills.Geometry.IntegralVarifold

noncomputable section

open MeasureTheory TopologicalSpace Set

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace Geometry

/-- Stratification package isolating the singular branching locus of a varifold. -/
structure Stratification [MeasurableSpace U] [BorelSpace U] (k : ℕ)
  (Vf : IntegralVarifold U V k) where
  
  -- The singular branching locus evaluating non-smooth gauge limit distributions
  branching_locus : Set U
  branching_locus_measurable : MeasurableSet branching_locus
  branching_locus_subset_carrier : branching_locus ⊆ Vf.carrier
  
  -- The regular manifold density is absolutely bounding the branched strata to have strictly 
  -- zero geometric mass (0-measure in exactly `k_real` Hausdorff dimension).
  is_null_stratum : Measure.hausdorffMeasure (k : ℝ) branching_locus = 0

  -- Weight-measure control of the singular locus by total mass.
  branching_weight_le_total_mass :
    (Vf.toVarifold.weightMeasure branching_locus) ≤ Vf.toVarifold.totalMass

end Geometry
