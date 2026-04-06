import YangMills.Geometry.IntegralVarifold

noncomputable section

open MeasureTheory TopologicalSpace Set Filter

namespace Geometry

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
variable [MeasurableSpace U] [BorelSpace U]
variable (k : ℕ)

/-- Weak-* convergence for integral varifolds in the induced mass topology. -/
def WeakStarConvergence
    (VfSeq : Nat → IntegralVarifold U U k) (Vf : IntegralVarifold U U k) : Prop :=
  Filter.Tendsto (fun n => VfSeq n) Filter.atTop (nhds Vf)

/--
Mean curvature represented as the Radon-Nikodym density of first variation
with respect to the weight measure.
-/
structure MeanCurvatureRadonDensity
  (Vf : Varifold U U k) where
  meanCurvature : U → U
  integrable_meanCurvature : Integrable meanCurvature Vf.weightMeasure
  firstVariation_density :
    ∀ X : TestVectorField U,
      firstVariation k Vf X =
        - ∫ x, inner (𝕜 := Real) (meanCurvature x) (X.toFun x) ∂Vf.weightMeasure

/-- Geometric Willmore energy defined from the mean-curvature Radon density. -/
def geometricWillmoreEnergy
    (Vf : Varifold U U k) (hH : MeanCurvatureRadonDensity k Vf) : Real :=
  ∫ x, ‖hH.meanCurvature x‖ ^ 2 ∂Vf.weightMeasure

lemma geometricWillmoreEnergy_nonneg
    (Vf : Varifold U U k) (hH : MeanCurvatureRadonDensity k Vf) :
    0 ≤ geometricWillmoreEnergy k Vf hH := by
  unfold geometricWillmoreEnergy
  refine integral_nonneg ?_
  intro x
  exact sq_nonneg ‖hH.meanCurvature x‖

lemma firstVariation_eq_meanCurvature_density
    (Vf : Varifold U U k) (hH : MeanCurvatureRadonDensity k Vf)
    (X : TestVectorField U) :
    firstVariation k Vf X =
      - ∫ x, inner (𝕜 := Real) (hH.meanCurvature x) (X.toFun x) ∂Vf.weightMeasure :=
  hH.firstVariation_density X

/--
Lower-semicontinuity of geometric Willmore energy under weak-* varifold convergence,
provided by the ambient GMT space interface.
-/
theorem geometricWillmoreEnergy_lowerSemicontinuous
    [GeometricMeasureTheorySpace U]
    (VfSeq : Nat → IntegralVarifold U U k) (Vf : IntegralVarifold U U k)
    (hConv : WeakStarConvergence k VfSeq Vf)
    (hHSeq : ∀ n, MeanCurvatureRadonDensity k (VfSeq n).toVarifold)
    (hH : MeanCurvatureRadonDensity k Vf.toVarifold) :
    geometricWillmoreEnergy k Vf.toVarifold hH
      ≤ Filter.liminf
          (fun n => geometricWillmoreEnergy k (VfSeq n).toVarifold (hHSeq n))
          Filter.atTop := by
  have hLsc :=
    GeometricMeasureTheorySpace.willmore_lower_semicontinuity
      (U := U) k VfSeq Vf
      (fun n => (hHSeq n).meanCurvature) hH.meanCurvature
      hConv
      (fun n => (hHSeq n).integrable_meanCurvature)
      hH.integrable_meanCurvature
  simpa [geometricWillmoreEnergy] using hLsc

end Geometry
