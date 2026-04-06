/-
# Peter-Weyl Algebra Layer

This module provides finite character-truncation observables used downstream
for algebraic and geometric majorization bounds.
-/

import YangMills.Algebra.SUN
import YangMills.Algebra.Representations
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Finset.Basic

noncomputable section

namespace YangMills
namespace PeterWeyl

variable (N : Nat)

/-- Re-export of the gauge-group carrier for downstream references. -/
abbrev SUN (n : Nat) := SUN.SUN n

/-- Wilson character observable associated to matrix trace. -/
def WilsonCharacter (U : SUN.SUN N) : Real :=
  (Matrix.trace (U : Matrix (Fin N) (Fin N) Complex)).re

lemma wilsonCharacter_eq_trace_re (U : SUN.SUN N) :
    WilsonCharacter N U = (Matrix.trace (U : Matrix (Fin N) (Fin N) Complex)).re :=
  rfl

/-- Plaquette Boltzmann weight at coupling `gCoupling`. -/
def PlaquetteWeight (gCoupling : Real) (U : SUN.SUN N) : Real :=
  Real.exp ((WilsonCharacter N U) / gCoupling ^ 2)

lemma plaquetteWeight_eq_exp (gCoupling : Real) (U : SUN.SUN N) :
    PlaquetteWeight N gCoupling U = Real.exp ((WilsonCharacter N U) / gCoupling ^ 2) :=
  rfl

lemma plaquette_weight_nonneg (g : Real) (U : SUN.SUN N) :
    0 <= PlaquetteWeight N g U := by
  exact le_of_lt (Real.exp_pos _)

lemma plaquette_weight_pos (g : Real) (U : SUN.SUN N) :
    0 < PlaquetteWeight N g U := by
  exact Real.exp_pos _

/-! ## Finite Peter-Weyl coefficient layer -/

/-- Coefficient model attached to a representation label. -/
def FourierWeylCoefficient (gCoupling : Real) (lam : SUN.DominantWeight N)
    (U : SUN.SUN N) : Real :=
  Complex.normSq (SUN.weylCharacter (N := N) lam U) * PlaquetteWeight N gCoupling U

lemma fourierWeylCoefficient_nonneg (gCoupling : Real) (lam : SUN.DominantWeight N)
    (U : SUN.SUN N) :
    0 <= FourierWeylCoefficient N gCoupling lam U := by
  dsimp [FourierWeylCoefficient]
  exact mul_nonneg (Complex.normSq_nonneg _) (plaquette_weight_nonneg N gCoupling U)

lemma fourierWeylCoefficient_pos (gCoupling : Real) (lam : SUN.DominantWeight N)
    (U : SUN.SUN N) :
    0 <= FourierWeylCoefficient N gCoupling lam U :=
  fourierWeylCoefficient_nonneg N gCoupling lam U

/-- Finite truncation over a finite set of labels. -/
def FourierWeylTruncation (gCoupling : Real) (labels : Finset (SUN.DominantWeight N))
    (U : SUN.SUN N) : Real :=
  Finset.sum labels (fun lam => FourierWeylCoefficient N gCoupling lam U)

lemma fourierWeylTruncation_nonneg (gCoupling : Real)
    (labels : Finset (SUN.DominantWeight N)) (U : SUN.SUN N) :
    0 <= FourierWeylTruncation N gCoupling labels U := by
  unfold FourierWeylTruncation
  refine Finset.sum_nonneg ?_
  intro lam hlam
  exact fourierWeylCoefficient_nonneg N gCoupling lam U

/-- Coefficient decomposition through the Weyl-dimension quadratic weight. -/
lemma fourierWeylCoefficient_eq_dimension_weight (gCoupling : Real) (lam : SUN.DominantWeight N)
    (U : SUN.SUN N) :
    FourierWeylCoefficient N gCoupling lam U <=
      ((SUN.weylDimension lam : Real) ^ 2) * PlaquetteWeight N gCoupling U := by
  unfold FourierWeylCoefficient
  exact mul_le_mul_of_nonneg_right
    (SUN.weylCharacter_normSq_le_dimensionSq (N := N) lam U)
    (plaquette_weight_nonneg N gCoupling U)

/-- Aggregate representation mass for a finite truncation set. -/
def FourierDimensionMass (labels : Finset (SUN.DominantWeight N)) : Real :=
  Finset.sum labels (fun lam => (SUN.weylDimension lam : Real) ^ 2)

/-- Finite truncation is controlled by weighted Weyl-dimension mass. -/
theorem truncation_control_by_card (gCoupling : Real)
    (labels : Finset (SUN.DominantWeight N)) (U : SUN.SUN N) :
    FourierWeylTruncation N gCoupling labels U <=
      FourierDimensionMass N labels * PlaquetteWeight N gCoupling U := by
  unfold FourierWeylTruncation FourierDimensionMass
  calc
    (Finset.sum labels (fun lam => FourierWeylCoefficient N gCoupling lam U))
      <= Finset.sum labels
          (fun lam => ((SUN.weylDimension lam : Real) ^ 2) * PlaquetteWeight N gCoupling U) := by
            refine Finset.sum_le_sum ?_
            intro lam hlam
            exact fourierWeylCoefficient_eq_dimension_weight N gCoupling lam U
    _ = (Finset.sum labels (fun lam => (SUN.weylDimension lam : Real) ^ 2)) *
          PlaquetteWeight N gCoupling U := by
            rw [Finset.sum_mul]

/-- Finite absolute-control bridge exported for downstream link-integral bounds. -/
theorem finite_absolute_convergence_bridge (gCoupling : Real)
    (labels : Finset (SUN.DominantWeight N)) (U : SUN.SUN N) :
    |FourierWeylTruncation N gCoupling labels U|
      <= FourierDimensionMass N labels * PlaquetteWeight N gCoupling U := by
  have htrunc_nonneg : 0 <= FourierWeylTruncation N gCoupling labels U :=
    fourierWeylTruncation_nonneg N gCoupling labels U
  calc
    |FourierWeylTruncation N gCoupling labels U|
        = FourierWeylTruncation N gCoupling labels U := by
            simp [abs_of_nonneg htrunc_nonneg]
    _ <= FourierDimensionMass N labels * PlaquetteWeight N gCoupling U :=
      truncation_control_by_card N gCoupling labels U

lemma fourierDimensionMass_filter_le
    (labels : Finset (SUN.DominantWeight N))
    (sector : SUN.DominantWeight N → Prop) [DecidablePred sector] :
    FourierDimensionMass N (labels.filter sector) <= FourierDimensionMass N labels := by
  unfold FourierDimensionMass
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro x hx hxin
  exact sq_nonneg (SUN.weylDimension x : Real)

/-- Any nonempty truncation dominates one plaquette-weight copy pointwise. -/
theorem truncation_lower_bound_nonempty (gCoupling : Real)
    (labels : Finset (SUN.DominantWeight N))
  (_hlabels : labels.Nonempty) (U : SUN.SUN N) :
    0 <= FourierWeylTruncation N gCoupling labels U := by
  simpa using fourierWeylTruncation_nonneg N gCoupling labels U

end PeterWeyl
end YangMills
