import YangMills.Geometry.DistributionalWillmore

noncomputable section
open MeasureTheory TopologicalSpace Set

variable {U V : Type*} [NormedAddCommGroup U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace Geometry

/-- `L^2`-integrability package on the branching stratum. -/
structure SingularIntegrability [MeasurableSpace U] [BorelSpace U]
  {k_dim : ℕ} (Vf : IntegralVarifold (V := V) (U := U) k_dim)
  (H : U → V)
  (strat : Stratification (U := U) (V := V) k_dim Vf) where
  
  -- Absolute boundedness on the branching locus.
  is_l2_integrable :
    Integrable (fun x => ‖H x‖^2)
      ((Geometry.Varifold.spatial_mass Vf.toVarifold).restrict strat.branching_locus)
  l2_bound_on_branching_locus :
    ∃ C : ℝ, 0 ≤ C ∧
      ∫ x in strat.branching_locus, ‖H x‖^2 ∂(Geometry.Varifold.spatial_mass Vf.toVarifold) ≤ C

end Geometry
