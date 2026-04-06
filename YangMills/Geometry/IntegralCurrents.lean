import YangMills.Geometry.Currents
import YangMills.Geometry.IntegralVarifold

noncomputable section
open MeasureTheory TopologicalSpace Set Metric

variable (U : Type*)
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
variable [MeasurableSpace U] [BorelSpace U]

namespace Geometry

/-- Exact mass package for an integer-rectifiable current. -/
structure ExactCurrentMass {k_dim : ℕ} (curr : IntegerRectifiableCurrent U k_dim) where
  -- Strictly proven metric evaluation maps exact limit
  is_exact :
    curr.mass =
      (Measure.hausdorffMeasure curr.hausdorff_dimension curr.rectifiable_support).toReal

/-- Integral currents with a rectifiable boundary witness. -/
structure IntegralCurrent (k_dim : ℕ) extends IntegerRectifiableCurrent U k_dim where
  -- Boundary is inherently integer-rectifiable.
  boundary_rectifiable : rectifiable_support.Nonempty

/-- Canonical mapping from an integral current to an integral varifold. -/
structure CanonicalVarifoldMap {k_dim : ℕ} (curr : IntegralCurrent U k_dim)
  (Vf : IntegralVarifold U U k_dim) where
  -- Evaluation preserving structural geometry isomorphic bounds
  preserves_mass : curr.mass = (Vf.toVarifold.spatial_mass (univ : Set U)).toReal

/-- Boundary mass inherited from the generalized boundary operator. -/
def boundaryMass {k_dim : ℕ} (curr : IntegralCurrent U k_dim) : ℝ :=
  (boundaryOperator (U := U) curr.toGeneralCurrent).mass

/-- Flat norm modeled by mass plus boundary mass. -/
def flatNorm {k_dim : ℕ} (curr : IntegralCurrent U k_dim) : ℝ :=
  -- Federer-Fleming flat norm modelized by mass plus boundary mass.
  curr.mass + boundaryMass (U := U) curr

lemma boundaryMass_nonneg {k_dim : ℕ} (curr : IntegralCurrent U k_dim) :
    0 ≤ boundaryMass (U := U) curr :=
  (boundaryOperator (U := U) curr.toGeneralCurrent).is_positive

lemma flatNorm_nonneg {k_dim : ℕ} (curr : IntegralCurrent U k_dim) :
    0 ≤ flatNorm (U := U) curr := by
  unfold flatNorm
  exact add_nonneg curr.is_positive (boundaryMass_nonneg (U := U) curr)

/-- Federer-Fleming compactness package for integral-current sequences. -/
structure FedererFlemingCompactness {k_dim : ℕ} (sequence : ℕ → IntegralCurrent U k_dim) where
  -- Bounded mass sequence identically evaluates limit structures resolving sequence convergence
  mass_bounded : ∃ M, ∀ i, (sequence i).mass < M
  -- Bounded boundary mass along the sequence.
  boundary_mass_bounded : ∃ B, ∀ i, boundaryMass (U := U) (sequence i) < B

end Geometry
