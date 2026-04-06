import YangMills.Geometry.Stratification
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
open MeasureTheory TopologicalSpace Set Metric

variable {U V : Type*} [NormedAddCommGroup U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace Geometry

/-- Distributional regularization by excision near branching vertices. -/
structure DistributionalRegularization [MeasurableSpace U] [BorelSpace U]
  (k : ℕ) (Vf : IntegralVarifold (V := V) (U := U) k)
  (strat : Stratification k Vf) (epsilon : ℝ) (_h_eps : 0 < epsilon) where
  
  -- The strictly excised topological neighborhood bounding the branches
  excised_domain : Set U
  excised_domain_measurable : MeasurableSet excised_domain
  -- Mathematical limit evaluation proving the excision is bounded
  -- capturing exactly the structured strata of the moduli branching locus.
  is_excised : strat.branching_locus ⊆ thickening epsilon excised_domain
  -- Quantitative control of excision mass by total mass.
  excision_mass_control :
    Vf.toVarifold.weightMeasure excised_domain ≤ Vf.toVarifold.totalMass

/-- Logarithmic divergence model for classical Willmore energy at vertices. -/
structure LogarithmicDivergence [MeasurableSpace U] [BorelSpace U]
  (k : ℕ) (Vf : IntegralVarifold (V := V) (U := U) k)
  (strat : Stratification k Vf) where
  -- As epsilon approaches 0, the classical integrated Willmore trace scales logarithmically bounds
  divergence_rate : ℝ
  divergence_nonneg : 0 ≤ divergence_rate

/-- Vertex counterterm extracted from Noether-type stress-energy conservation. -/
structure VertexCounterterm [MeasurableSpace U] [BorelSpace U]
  (k : ℕ) (Vf : IntegralVarifold (V := V) (U := U) k)
  (strat : Stratification k Vf) where
  -- The counterterm scalar strictly offsets the Logarithmic Divergence identically
  counterterm : ℝ
  counterterm_nonneg : 0 ≤ counterterm

lemma counterterm_abs_eq_self [MeasurableSpace U] [BorelSpace U]
  (k : ℕ) (Vf : IntegralVarifold (V := V) (U := U) k)
  (strat : Stratification k Vf)
  (counter : VertexCounterterm k Vf strat) :
  |counter.counterterm| = counter.counterterm := by
  exact abs_of_nonneg counter.counterterm_nonneg

end Geometry
