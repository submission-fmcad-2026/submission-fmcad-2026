import Mathlib.MeasureTheory.Measure.MutuallySingular
import YangMills.Geometry.Varifold
import YangMills.Geometry.FirstVariation

noncomputable section

open MeasureTheory TopologicalSpace Set
open Grassmannian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {U : Type*} [TopologicalSpace U]
variable (k : ℕ)

namespace Geometry

/-- Lebesgue-Radon-Nikodym style decomposition of first variation data. -/
structure VariationDecomposition [MeasurableSpace U] [BorelSpace U] (Vf : Varifold U V k) where
  -- Absolutely continuous functional generalized curvature
  H : U → V
  H_integrable : Integrable H Vf.spatial_mass
  
  -- Mutually singular intersection manifold
  singular_measure : Measure U
  is_singular : Measure.MutuallySingular singular_measure Vf.spatial_mass
  singular_measure_finite : singular_measure Set.univ < (⊤ : ENNReal)
  -- Quantitative control coupling absolute and singular parts.
  curvature_L1_control :
    ∫ x, ‖H x‖ ∂Vf.spatial_mass ≤
      Vf.totalMass.toReal + (singular_measure Set.univ).toReal

lemma VariationDecomposition.H_aestronglyMeasurable
    [MeasurableSpace U] [BorelSpace U]
    {Vf : Varifold U V k}
    (decomp : VariationDecomposition k Vf) :
    AEStronglyMeasurable decomp.H Vf.spatial_mass :=
  decomp.H_integrable.aestronglyMeasurable

lemma VariationDecomposition.singular_measure_univ_lt_top
    [MeasurableSpace U] [BorelSpace U]
    {Vf : Varifold U V k}
    (decomp : VariationDecomposition k Vf) :
    decomp.singular_measure Set.univ < (⊤ : ENNReal) :=
  decomp.singular_measure_finite

lemma VariationDecomposition.curvature_L1_nonneg
    [MeasurableSpace U] [BorelSpace U]
    {Vf : Varifold U V k}
    (decomp : VariationDecomposition k Vf) :
    0 ≤ ∫ x, ‖decomp.H x‖ ∂Vf.spatial_mass := by
  refine integral_nonneg ?_
  intro x
  exact norm_nonneg _

lemma VariationDecomposition.curvature_L1_le_total_control
  [MeasurableSpace U] [BorelSpace U]
    {Vf : Varifold U V k}
    (decomp : VariationDecomposition k Vf) :
    ∫ x, ‖decomp.H x‖ ∂Vf.spatial_mass ≤
      Vf.totalMass.toReal + (decomp.singular_measure Set.univ).toReal :=
  decomp.curvature_L1_control

end Geometry
