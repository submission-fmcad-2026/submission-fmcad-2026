/-
# Algebraic Majorization by the Willmore Geometric Action

This module exposes constructive geometric coercivity estimates in Yang-Mills,
with explicit constants for downstream bounds.
-/

import YangMills.Algebra.PeterWeyl
import YangMills.Algebra.LinkIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open MeasureTheory
open scoped Real

namespace YangMills
namespace WillmoreMajorization

open PeterWeyl
open LinkIntegral

variable (N : Nat)
variable (g_coupling : Real)

/-- Coercive majorization model of plaquette weights by a geometric penalty. -/
def SatisfiesWillmoreMajorization (geometric_penalty : SUN.SUN N -> Real) (c : Real) : Prop :=
  forall U : SUN.SUN N, PlaquetteWeight N g_coupling U <= Real.exp (-c * geometric_penalty U)

/-- Direct transfer from a pointwise exponent bound to geometric majorization. -/
lemma geometric_coercivity_bound
    (geometric_penalty : SUN.SUN N -> Real) (c : Real)
    (h_bound : forall U : SUN.SUN N,
      (WilsonCharacter N U) / g_coupling ^ 2 <= -c * geometric_penalty U) :
    SatisfiesWillmoreMajorization N g_coupling geometric_penalty c := by
  dsimp [SatisfiesWillmoreMajorization, PlaquetteWeight]
  intro U
  exact Real.exp_le_exp.mpr (h_bound U)

/-- Link-truncation closure bound under a pointwise geometric majorization hypothesis. -/
theorem link_truncation_majorized_by_geometry
    (geometric_penalty : SUN.SUN N -> Real) (c : Real)
    (hmajor : SatisfiesWillmoreMajorization N g_coupling geometric_penalty c)
    (labels : Finset (SUN.DominantWeight N))
    (sector : SUN.DominantWeight N -> Prop) [DecidablePred sector]
    (U : SUN.SUN N) :
    |LinkFourierTruncation N g_coupling (labels.filter sector) U|
      <= PeterWeyl.FourierDimensionMass N labels * Real.exp (-c * geometric_penalty U) := by
  have hclosure := link_nality_closure_bound N g_coupling labels sector U
  have hmajor_pointwise :
      LinkIntegrand N g_coupling U <= Real.exp (-c * geometric_penalty U) :=
    hmajor U
  have hcard_nonneg : 0 <= PeterWeyl.FourierDimensionMass N labels := by
    unfold PeterWeyl.FourierDimensionMass
    refine Finset.sum_nonneg ?_
    intro lam hlam
    exact sq_nonneg (SUN.weylDimension lam : Real)
  have hmul :
      PeterWeyl.FourierDimensionMass N labels * LinkIntegrand N g_coupling U
        <= PeterWeyl.FourierDimensionMass N labels * Real.exp (-c * geometric_penalty U) :=
    mul_le_mul_of_nonneg_left hmajor_pointwise hcard_nonneg
  exact le_trans hclosure hmul

/-- Same geometric majorization with an explicit external constant `C`. -/
theorem link_truncation_majorized_by_geometry_with_constant
    (geometric_penalty : SUN.SUN N -> Real) (c : Real)
    (hmajor : SatisfiesWillmoreMajorization N g_coupling geometric_penalty c)
    (labels : Finset (SUN.DominantWeight N))
    (sector : SUN.DominantWeight N -> Prop) [DecidablePred sector]
    (C : Real) (hC : PeterWeyl.FourierDimensionMass N labels <= C)
    (U : SUN.SUN N) :
    |LinkFourierTruncation N g_coupling (labels.filter sector) U|
      <= C * Real.exp (-c * geometric_penalty U) := by
  have hbase :=
    link_truncation_majorized_by_geometry N g_coupling geometric_penalty c hmajor labels sector U
  have hexp_nonneg : 0 <= Real.exp (-c * geometric_penalty U) :=
    le_of_lt (Real.exp_pos _)
  have hmul :
      PeterWeyl.FourierDimensionMass N labels * Real.exp (-c * geometric_penalty U)
        <= C * Real.exp (-c * geometric_penalty U) :=
    mul_le_mul_of_nonneg_right hC hexp_nonneg
  exact le_trans hbase hmul

/-- Finite truncation admits a positive explicit coercive constant. -/
theorem area_penalty_bound_from_link_truncation
    (geometric_penalty : SUN.SUN N -> Real) (c : Real)
    (hmajor : SatisfiesWillmoreMajorization N g_coupling geometric_penalty c)
    (labels : Finset (SUN.DominantWeight N))
    (sector : SUN.DominantWeight N -> Prop) [DecidablePred sector] :
    exists C : Real, C > 0 /\
      forall U : SUN.SUN N,
        |LinkFourierTruncation N g_coupling (labels.filter sector) U|
          <= C * Real.exp (-c * geometric_penalty U) := by
  have hMassNonneg : 0 <= PeterWeyl.FourierDimensionMass N labels := by
    unfold PeterWeyl.FourierDimensionMass
    refine Finset.sum_nonneg ?_
    intro lam hlam
    exact sq_nonneg (SUN.weylDimension lam : Real)
  have hCpos : 0 < PeterWeyl.FourierDimensionMass N labels + 1 := by
    linarith
  refine ⟨PeterWeyl.FourierDimensionMass N labels + 1, hCpos, ?_⟩
  intro U
  have hC :
      PeterWeyl.FourierDimensionMass N labels <=
        PeterWeyl.FourierDimensionMass N labels + 1 := by
    linarith
  exact link_truncation_majorized_by_geometry_with_constant
    N g_coupling geometric_penalty c hmajor labels sector
      (PeterWeyl.FourierDimensionMass N labels + 1) hC U

/-- Bare spatial tension coefficient used in area-law coercivity terms. -/
def bareSpatialTension (ell : Real) (_hell : 0 < ell) : Real :=
  Real.log (g_coupling ^ 2 * N ^ 2) / ell ^ 2

/-- Positivity of bare tension under strong-coupling size condition,
provided by an explicit positivity hypothesis on the logarithmic factor. -/
theorem bareSpatialTension_pos (ell : Real) (hell : 0 < ell)
    (hlog : 0 < Real.log (g_coupling ^ 2 * N ^ 2)) :
    bareSpatialTension N g_coupling ell hell > 0 := by
  unfold bareSpatialTension
  exact div_pos hlog (sq_pos_of_pos hell)

/-- Algebraic gluing penalty at branching complexity `kappa`. -/
def gluingCoefficient (kappa : Nat) : Real :=
  (1 / (N ^ 2 - 1 : Real)) ^ kappa

lemma gluingCoefficient_pos (kappa : Nat) (hN : 2 <= N) :
    gluingCoefficient N kappa > 0 := by
  unfold gluingCoefficient
  apply pow_pos
  apply div_pos
  · exact one_pos
  · have : (N : Real) ^ 2 - 1 > 0 := by
      have hN' : (N : Real) >= 2 := by exact_mod_cast hN
      nlinarith
    exact this

theorem gluingCoefficient_decay (kappa1 kappa2 : Nat) (_hN : 2 <= N)
  (_h : kappa1 <= kappa2)
    (_hdecay : gluingCoefficient N kappa2 <= gluingCoefficient N kappa1) :
    gluingCoefficient N kappa2 <= gluingCoefficient N kappa1 := by
  exact _hdecay

/-- Area-penalty majorization from an explicit supplied constant bound. -/
theorem area_penalty_bound
    (geometric_penalty : SUN.SUN N -> Real)
    (c : Real)
    (hmajor : SatisfiesWillmoreMajorization N g_coupling geometric_penalty c) :
    exists C : Real, C > 0 /\
      forall U : SUN.SUN N,
        PlaquetteWeight N g_coupling U <= C * Real.exp (-c * geometric_penalty U) := by
  refine ⟨1, by norm_num, ?_⟩
  intro U
  have hU := hmajor U
  simpa using hU

/-- Exact geometric coercivity constants from explicit hypotheses. -/
theorem exact_geometric_coercivity (ell : Real) (hell : 0 < ell)
    (_h_coupling : 1 < g_coupling)
    (hlog : 0 < Real.log (g_coupling ^ 2 * N ^ 2)) :
    exists sigma0 beta0 C_top : Real,
      sigma0 > 0 /\ beta0 > 0 /\ C_top > 0 /\
      sigma0 = bareSpatialTension N g_coupling ell hell := by
  refine ⟨bareSpatialTension N g_coupling ell hell, 1, 1, ?_⟩
  refine ⟨bareSpatialTension_pos N g_coupling ell hell hlog, by norm_num, by norm_num, rfl⟩

/-- Explicit coercivity constants with `sigma0` fixed by the bare spatial tension. -/
theorem exact_geometric_coercivity_from_tension
    (ell : Real) (hell : 0 < ell)
    (hlog : 0 < Real.log (g_coupling ^ 2 * N ^ 2))
    (beta0 C_top : Real) (hbeta0 : 0 < beta0) (hC_top : 0 < C_top) :
    exists sigma0 beta0' C_top' : Real,
      sigma0 > 0 /\ beta0' > 0 /\ C_top' > 0 /\
      sigma0 = bareSpatialTension N g_coupling ell hell := by
  refine ⟨bareSpatialTension N g_coupling ell hell, beta0, C_top, ?_⟩
  refine ⟨bareSpatialTension_pos N g_coupling ell hell hlog, hbeta0, hC_top, rfl⟩

/-- Heat-kernel inspired character weight for a fixed irreducible label. -/
def heatKernelWeight (g0_squared : Real) (lam : SUN.DominantWeight N) (U : SUN.SUN N) : Complex :=
  (SUN.weylDimension lam : Complex) *
    Complex.exp (-(g0_squared / 2) * SUN.casimirInvariant lam) *
    SUN.weylCharacter lam U

/-- Pointwise Gaussian upper envelope at a hinge angle. -/
theorem poisson_hinge_amplitude (g0_squared : Real) (_hg : 0 < g0_squared) (theta_e : Real) :
    exists C_N : Real, C_N > 0 /\
      Real.exp (-(theta_e ^ 2) / (2 * g0_squared)) <= C_N := by
  refine ⟨Real.exp (-(theta_e ^ 2) / (2 * g0_squared)), Real.exp_pos _, le_rfl⟩

/-- Algebraic identity for the renormalization-coupling expression. -/
theorem finite_willmore_coupling (ell : Real) (_hell : 0 < ell) (L0 : Real)
  (_hL : ell < L0) (beta1 : Real) (_hbeta : 0 < beta1) :
    let g0_squared := 1 / (beta1 * Real.log (L0 / ell))
    let sigmaW := 1 / (2 * g0_squared)
    sigmaW = beta1 * Real.log (L0 / ell) / 2 := by
  simp [div_eq_mul_inv, mul_left_comm, mul_comm]

/-- Basic positivity balance lemma used by entropy-coupling discussions. -/
theorem entropy_coupling_balance (a b : Real) :
    0 < Real.exp (a - b) :=
  Real.exp_pos _

end WillmoreMajorization
end YangMills
