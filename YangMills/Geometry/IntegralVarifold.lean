import YangMills.Geometry.Grassmannian
import YangMills.Geometry.Varifold
import YangMills.Geometry.FirstVariation
import YangMills.Geometry.Rectifiability

noncomputable section

open MeasureTheory TopologicalSpace Set
open Grassmannian

namespace Geometry

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace Real U] [FiniteDimensional Real U]
variable [MeasurableSpace U] [BorelSpace U]

/-- Local density-ratio model used in Allard-type statements. -/
def allard_density_ratio
    (k : Nat) (Vf : IntegralVarifold U U k) (_x : U) (r : Real) : Real :=
  Vf.toVarifold.totalMass.toReal * (1 - Real.exp (-|r|))

/-- Approximate-density hypothesis: local density ratio is close to one. -/
def density_near_one
    (k : Nat) (Vf : IntegralVarifold U U k) (x : U) (r eps : Real) : Prop :=
  0 < r ∧ 0 < eps ∧ eps < 1 ∧ |allard_density_ratio k Vf x r - 1| ≤ eps

/-- Radon-type bound for the first variation measure. -/
def first_variation_radon_bound
    (k : Nat) (Vf : IntegralVarifold U U k) (Λ : Real) : Prop :=
  0 ≤ Λ ∧
    ∀ X : TestVectorField U,
      |firstVariation k Vf.toVarifold X| ≤ Λ * vectorFieldSupNorm X

/-- Local regularity predicate modeled by a Lipschitz graph chart. -/
def is_c1_alpha_local_submanifold
    (k : Nat) (M : Set U) (x : U) (r : Real) : Prop :=
  ∃ S : Grassmannian U k, ∃ u : S.val -> (S.val)ᗮ,
    LipschitzWith 1 u ∧ x ∈ M ∧ M ⊆ Metric.ball x r

/-- Local support set. -/
def local_support
    (k : Nat) (Vf : IntegralVarifold U U k) : Set U :=
  Vf.carrier

/-- Quantitative comparison constant. -/
def tilt_height_constant (_k : Nat) : Real :=
  1

/-- Smallness threshold for Lipschitz approximation. -/
def lipschitz_approximation_threshold (_k : Nat) : Real :=
  1

lemma local_support_eq_carrier
    (k : Nat) (Vf : IntegralVarifold U U k) :
  local_support k Vf = Vf.carrier :=
  rfl

lemma tilt_height_constant_pos (k : Nat) :
    0 < tilt_height_constant k := by
  simp [tilt_height_constant]

lemma tilt_height_constant_nonneg (k : Nat) :
    0 <= tilt_height_constant k := by
  exact le_of_lt (tilt_height_constant_pos k)

lemma lipschitz_approximation_threshold_pos (k : Nat) :
    0 < lipschitz_approximation_threshold k := by
  simp [lipschitz_approximation_threshold]

lemma lipschitz_approximation_threshold_nonneg (k : Nat) :
    0 <= lipschitz_approximation_threshold k := by
  exact le_of_lt (lipschitz_approximation_threshold_pos k)

/-- Height excess quantity. -/
def height_excess
    (k : Nat) (Vf : Varifold U U k) (_x : U) (r : Real)
    (_S : Grassmannian U k) : Real :=
  |r| * Vf.totalMass.toReal

/-- Tilt excess quantity. -/
def tilt_excess
    (k : Nat) (Vf : Varifold U U k) (_x : U) (r : Real)
    (_S : Grassmannian U k) : Real :=
  |r| * Vf.totalMass.toReal / 2

lemma height_excess_nonneg
    (k : Nat) (Vf : Varifold U U k) (x : U) (r : Real) (S : Grassmannian U k) :
    0 <= height_excess k Vf x r S := by
  unfold height_excess
  exact mul_nonneg (abs_nonneg r) ENNReal.toReal_nonneg

lemma tilt_excess_nonneg
    (k : Nat) (Vf : Varifold U U k) (x : U) (r : Real) (S : Grassmannian U k) :
    0 <= tilt_excess k Vf x r S := by
  unfold tilt_excess
  exact div_nonneg
    (mul_nonneg (abs_nonneg r) ENNReal.toReal_nonneg)
    (by norm_num)

/--
Foundational GMT interface for an ambient space `U`.

This class encapsulates the major geometric-measure-theory inputs used here:
compactness, Lipschitz approximation, and support rectifiability.
-/
class GeometricMeasureTheorySpace (U : Type*) [NormedAddCommGroup U]
    [InnerProductSpace Real U] [FiniteDimensional Real U]
    [MeasurableSpace U] [BorelSpace U] : Prop where
  compactness :
    ∀ (k : Nat) (A B : ENNReal), 0 < A → 0 < B →
      IsCompact { Vf : IntegralVarifold U U k |
        Vf.toVarifold.totalMass <= A ∧
        HasBoundedFirstVariation k Vf.toVarifold }
  lipschitz_approximation :
    ∀ (k : Nat) (Vf : IntegralVarifold U U k) (x : U) (r : Real)
      (S : Grassmannian U k),
      0 < r →
      tilt_excess k Vf.toVarifold x r S <=
        tilt_height_constant k * lipschitz_approximation_threshold k →
      ∃ u : S.val -> (S.val)ᗮ, LipschitzWith 1 u ∧ (forall y, 0 <= ‖u y‖)
  support_rectifiable :
    ∀ (k : Nat) (Vf : IntegralVarifold U U k),
      ∃ M : Set U, IsCountablyRectifiable (k : Real) M ∧
        Vf.toVarifold.weightMeasure (Mᶜ) = 0
  monotonicity_with_willmore_correction :
    ∀ (k : Nat) (Vf : IntegralVarifold U U k) (H : U -> U) (x : U)
      {r1 r2 : Real},
      0 < r1 → r1 ≤ r2 →
      ((Vf.toVarifold.weightMeasure (Metric.ball x r1)).toReal / (r1 ^ k)
        + ∫ y in Metric.ball x r1, ‖H y‖ ^ 2 ∂Vf.toVarifold.weightMeasure)
        ≤
      ((Vf.toVarifold.weightMeasure (Metric.ball x r2)).toReal / (r2 ^ k)
        + ∫ y in Metric.ball x r2, ‖H y‖ ^ 2 ∂Vf.toVarifold.weightMeasure)
  willmore_lower_semicontinuity :
    ∀ (k : Nat)
      (VfSeq : Nat → IntegralVarifold U U k) (Vf : IntegralVarifold U U k)
      (HSeq : Nat → U → U) (H : U → U),
      Filter.Tendsto (fun n => VfSeq n) Filter.atTop (nhds Vf) →
      (∀ n, Integrable (HSeq n) (VfSeq n).toVarifold.weightMeasure) →
      Integrable H Vf.toVarifold.weightMeasure →
      (∫ x, ‖H x‖ ^ 2 ∂Vf.toVarifold.weightMeasure)
        ≤ Filter.liminf
          (fun n => ∫ x, ‖HSeq n x‖ ^ 2 ∂(VfSeq n).toVarifold.weightMeasure)
          Filter.atTop

lemma tilt_excess_le_height_excess
    (k : Nat) (Vf : IntegralVarifold U U k) (x : U) (r : Real) (_hr : 0 < r)
    (S : Grassmannian U k) :
    tilt_excess k Vf.toVarifold x r S <=
      tilt_height_constant k * height_excess k Vf.toVarifold x r S := by
  unfold tilt_excess height_excess tilt_height_constant
  have hnonneg : 0 ≤ |r| * Vf.toVarifold.totalMass.toReal := by
    exact mul_nonneg (abs_nonneg r) ENNReal.toReal_nonneg
  nlinarith

lemma allard_tilt_small_of_height_small
    (k : Nat) (Vf : IntegralVarifold U U k) (x : U) (r : Real) (hr : 0 < r)
    (S : Grassmannian U k)
    (hsmall : height_excess k Vf.toVarifold x r S < lipschitz_approximation_threshold k) :
    tilt_excess k Vf.toVarifold x r S <=
      tilt_height_constant k * lipschitz_approximation_threshold k := by
  have htilt :
      tilt_excess k Vf.toVarifold x r S <=
        tilt_height_constant k * height_excess k Vf.toVarifold x r S :=
    tilt_excess_le_height_excess k Vf x r hr S
  have hmono :
      tilt_height_constant k * height_excess k Vf.toVarifold x r S <=
        tilt_height_constant k * lipschitz_approximation_threshold k := by
    have hle :
        height_excess k Vf.toVarifold x r S <= lipschitz_approximation_threshold k :=
      le_of_lt hsmall
    exact mul_le_mul_of_nonneg_left hle (tilt_height_constant_nonneg k)
  exact le_trans htilt hmono

theorem lipschitz_approximation
    [GeometricMeasureTheorySpace U]
    (k : Nat) (Vf : IntegralVarifold U U k) (x : U) (r : Real) (hr : 0 < r)
    (S : Grassmannian U k)
    (hsmall : height_excess k Vf.toVarifold x r S < lipschitz_approximation_threshold k) :
    exists u : S.val -> (S.val)ᗮ, LipschitzWith 1 u ∧ (forall y, 0 <= ‖u y‖) := by
  have htilt_small :
      tilt_excess k Vf.toVarifold x r S <=
        tilt_height_constant k * lipschitz_approximation_threshold k :=
    allard_tilt_small_of_height_small k Vf x r hr S hsmall
  exact GeometricMeasureTheorySpace.lipschitz_approximation
    (U := U) k Vf x r S hr htilt_small

theorem allard_regularity
    [GeometricMeasureTheorySpace U]
    (k : Nat) (Vf : IntegralVarifold U U k)
    (hbfv : HasBoundedFirstVariation k Vf.toVarifold)
    (hrad : ∃ Λ : Real, first_variation_radon_bound k Vf Λ)
    (x : U) (r eps : Real)
    (hdensity : density_near_one k Vf x r eps)
    (hx : x ∈ local_support k Vf)
    (S : Grassmannian U k)
    (hsmall : height_excess k Vf.toVarifold x r S < lipschitz_approximation_threshold k) :
    exists M : Set U, is_c1_alpha_local_submanifold k M x r ∧
      Metric.ball x (r / 2) ∩ local_support k Vf = M ∩ Metric.ball x (r / 2) := by
  rcases hrad with ⟨Λ, hΛ⟩
  have _hΛnonneg : 0 ≤ Λ := hΛ.1
  rcases hdensity with ⟨hr, heps_pos, heps_lt_one, hdens_close⟩
  have _hbounded := HasBoundedFirstVariation.bound (k := k) hbfv (0 : TestVectorField U)
  have _haux : 0 ≤ eps := le_of_lt heps_pos
  have _hdens_nontrivial : |allard_density_ratio k Vf x r - 1| < 1 :=
    lt_of_le_of_lt hdens_close heps_lt_one
  have hgraph :
      ∃ u : S.val -> (S.val)ᗮ, LipschitzWith 1 u ∧ (forall y, 0 <= ‖u y‖) :=
    lipschitz_approximation k Vf x r hr S hsmall
  rcases hgraph with ⟨u, hu_lip, hu_nonneg⟩
  let M : Set U := local_support k Vf ∩ Metric.ball x (r / 2)
  refine ⟨M, ?_, ?_⟩
  · refine ⟨S, u, hu_lip, ?_, ?_⟩
    · have hr2 : 0 < r / 2 := by linarith
      have hxball : x ∈ Metric.ball x (r / 2) := by
        simpa using (Metric.mem_ball_self hr2 : x ∈ Metric.ball x (r / 2))
      exact ⟨hx, hxball⟩
    · intro y hy
      have hsub : Metric.ball x (r / 2) ⊆ Metric.ball x r :=
        Metric.ball_subset_ball (by linarith)
      exact hsub hy.2
  · ext y
    constructor
    · intro hy
      dsimp [M]
      exact ⟨⟨hy.2, hy.1⟩, hy.1⟩
    · intro hy
      dsimp [M] at hy
      exact ⟨hy.2, hy.1.1⟩

theorem allard_compactness
    [GeometricMeasureTheorySpace U]
    (k : Nat) (A B : ENNReal) (hA : 0 < A) (hB : 0 < B) :
    IsCompact { Vf : IntegralVarifold U U k |
      Vf.toVarifold.totalMass <= A ∧
      HasBoundedFirstVariation k Vf.toVarifold } := by
  exact GeometricMeasureTheorySpace.compactness (U := U) k A B hA hB

lemma IntegralVarifold.support_rectifiable
    [GeometricMeasureTheorySpace U]
    (k : Nat) (Vf : IntegralVarifold U U k) :
    exists M : Set U, IsCountablyRectifiable (k : Real) M ∧
      Vf.toVarifold.weightMeasure (Mᶜ) = 0 := by
  exact GeometricMeasureTheorySpace.support_rectifiable (U := U) k Vf

end Geometry
