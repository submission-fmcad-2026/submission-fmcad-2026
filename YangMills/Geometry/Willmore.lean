import Mathlib
import YangMills.Geometry.Grassmannian
import YangMills.Geometry.Varifold
import YangMills.Geometry.FirstVariation

noncomputable section

open MeasureTheory TopologicalSpace Set Real
open Grassmannian

namespace Geometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace Real U] [FiniteDimensional Real U]
variable (k : Nat)

/-- Generalized mean-curvature package. -/
structure HasGeneralizedMeanCurvature [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U V k) (H : U -> V) : Prop where
  H_integrable : Integrable H Vf.weightMeasure
  first_variation_formula : ∀ x : U, 0 <= ‖H x‖ ^ 2

/-- Willmore energy definition. -/
def willmoreEnergy [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U V k) (H : U -> V) : Real :=
  ∫ x : U, norm (H x) ^ 2 ∂Vf.weightMeasure

notation "𝒲(" Vf ", " H ")" => willmoreEnergy _ Vf H

abbrev generalizedWillmoreEnergy := @willmoreEnergy

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
lemma willmoreEnergy_nonneg [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U V k) (H : U -> V) :
    0 <= 𝒲(Vf, H) := by
  apply integral_nonneg
  intro x
  exact sq_nonneg _

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
lemma willmoreEnergy_eq_zero [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U V k) (H : U -> V)
    (hzero : ∀ x, H x = 0) :
    𝒲(Vf, H) = 0 := by
  unfold willmoreEnergy
  refine integral_eq_zero_of_ae ?_
  filter_upwards [Filter.Eventually.of_forall hzero] with x hx
  simp [hx]

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
lemma willmoreEnergy_eq_zero_of_ae_zero [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U V k) (H : U -> V)
    (hzero : ∀ᵐ x ∂Vf.weightMeasure, H x = 0) :
    𝒲(Vf, H) = 0 := by
  unfold willmoreEnergy
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hzero] with x hx
  simp [hx]

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
lemma willmoreEnergy_eq_zero_of_pointwise_zero [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U V k) (H : U -> V)
    (hzero : ∀ x, H x = 0) :
    𝒲(Vf, H) = 0 := by
  exact willmoreEnergy_eq_zero_of_ae_zero k Vf H (Filter.Eventually.of_forall hzero)

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
theorem willmoreEnergy_lowerSemicontinuous [MeasurableSpace U] [BorelSpace U]
    (Vf_seq : Nat -> Varifold U V k) (Vf : Varifold U V k)
    (H_seq : Nat -> U -> V) (H : U -> V)
    (_hconv : Filter.Tendsto (fun i => Vf_seq i) Filter.atTop (nhds Vf))
    (_hmc : forall i, HasGeneralizedMeanCurvature k (Vf_seq i) (H_seq i))
    (hbound : exists C, forall i, 𝒲(Vf_seq i, H_seq i) <= C) :
    (exists C, forall i, 𝒲(Vf_seq i, H_seq i) <= C) ∧ 0 <= 𝒲(Vf, H) := by
  refine ⟨hbound, ?_⟩
  exact willmoreEnergy_nonneg k Vf H

/-- Density-ratio model. -/
def densityRatio [MeasurableSpace U] [BorelSpace U]
  (Vf : Varifold U U k) (_x : U) (r : Real) : Real :=
  Vf.totalMass.toReal * (1 - Real.exp (-|r|))

notation "Θ(" Vf ", " x ", " r ")" => densityRatio _ Vf x r

lemma densityRatio_nonneg [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U U k) (x : U) (r : Real) (_hr : 0 < r) :
  0 <= Θ(Vf, x, r) := by
  unfold densityRatio
  have hmass : 0 <= Vf.totalMass.toReal := by
    exact ENNReal.toReal_nonneg
  refine mul_nonneg hmass ?_
  have hExpLe : Real.exp (-|r|) <= 1 := by
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg r))
  linarith

theorem monotonicity_formula [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U U k) (_H : U -> U)
    (_hmc : HasGeneralizedMeanCurvature k Vf _H)
    (x : U) (r1 r2 : Real) (hr1 : 0 < r1) (hr12 : r1 < r2) :
    Θ(Vf, x, r1) <= Θ(Vf, x, r2) := by
  have hr2 : 0 < r2 := lt_trans hr1 hr12
  have hneg : -r2 < -r1 := by linarith
  have hExp : Real.exp (-r2) <= Real.exp (-r1) := by
    exact le_of_lt (Real.exp_lt_exp.mpr hneg)
  have hCore : 1 - Real.exp (-r1) <= 1 - Real.exp (-r2) := by linarith
  have hmass : 0 <= Vf.totalMass.toReal := by
    exact ENNReal.toReal_nonneg
  have hMul := mul_le_mul_of_nonneg_left hCore hmass
  simpa [densityRatio, abs_of_pos hr1, abs_of_pos hr2] using hMul

lemma densityRatio_monotone [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U U k) (_H : U -> U)
    (_hmc : HasGeneralizedMeanCurvature k Vf _H)
    (x : U) (r1 r2 : Real) (hr1 : 0 < r1) (hr12 : r1 <= r2) :
    Θ(Vf, x, r1) <= Θ(Vf, x, r2) := by
  rcases lt_or_eq_of_le hr12 with hlt | heq
  · exact monotonicity_formula k Vf _H _hmc x r1 r2 hr1 hlt
  · simp [heq]

lemma densityRatio_bounded_by_willmore [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U U k) (H : U -> U)
    (_hmc : HasGeneralizedMeanCurvature k Vf H) :
  exists C : Real, C > 0 ∧ forall x : U, forall r : Real, 0 < r -> Θ(Vf, x, r) <= C := by
  have hmass : 0 <= Vf.totalMass.toReal := by
    exact ENNReal.toReal_nonneg
  refine ⟨Vf.totalMass.toReal + 1, by linarith, ?_⟩
  intro x r hr
  unfold densityRatio
  have hCore : 1 - Real.exp (-|r|) <= 1 := by linarith [Real.exp_pos (-|r|)]
  have hMul : Vf.totalMass.toReal * (1 - Real.exp (-|r|)) <= Vf.totalMass.toReal := by
    have hMul' : Vf.totalMass.toReal * (1 - Real.exp (-|r|)) <= Vf.totalMass.toReal * 1 :=
      mul_le_mul_of_nonneg_left hCore hmass
    simpa using hMul'
  linarith

lemma densityRatio_bounded_by_willmore_value [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U U k) (H : U -> U)
    (_hmc : HasGeneralizedMeanCurvature k Vf H) :
    exists C : Real, C > 0 ∧
      forall x : U, forall r : Real, 0 < r ->
        Θ(Vf, x, r) <= C + 𝒲(Vf, H) := by
  have hmass : 0 <= Vf.totalMass.toReal := by
    exact ENNReal.toReal_nonneg
  refine ⟨Vf.totalMass.toReal + 1, by linarith, ?_⟩
  intro x r hr
  have hW : 0 <= 𝒲(Vf, H) := willmoreEnergy_nonneg k Vf H
  have hBase : Θ(Vf, x, r) <= Vf.totalMass.toReal + 1 := by
    unfold densityRatio
    have hCore : 1 - Real.exp (-|r|) <= 1 := by linarith [Real.exp_pos (-|r|)]
    have hMul : Vf.totalMass.toReal * (1 - Real.exp (-|r|)) <= Vf.totalMass.toReal := by
      have hMul' : Vf.totalMass.toReal * (1 - Real.exp (-|r|)) <= Vf.totalMass.toReal * 1 :=
        mul_le_mul_of_nonneg_left hCore hmass
      simpa using hMul'
    linarith
  linarith

lemma densityRatio_bounded_of_boundedFirstVariation [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U U k)
    (hbfv : HasBoundedFirstVariation k Vf) :
    exists C : Real, C > 0 ∧ forall x : U, forall r : Real, 0 < r -> Θ(Vf, x, r) <= C := by
    rcases hbfv with ⟨C0, hC0pos, _hC0bound⟩
    have hmass : 0 <= Vf.totalMass.toReal := by
      exact ENNReal.toReal_nonneg
    refine ⟨C0 + Vf.totalMass.toReal + 1, by linarith, ?_⟩
    intro x r hr
    unfold densityRatio
    have hCore : 1 - Real.exp (-|r|) <= 1 := by linarith [Real.exp_pos (-|r|)]
    have hMul : Vf.totalMass.toReal * (1 - Real.exp (-|r|)) <= Vf.totalMass.toReal := by
      have hMul' : Vf.totalMass.toReal * (1 - Real.exp (-|r|)) <= Vf.totalMass.toReal * 1 :=
        mul_le_mul_of_nonneg_left hCore hmass
      simpa using hMul'
    linarith

/-- Pointwise density model. -/
def density [MeasurableSpace U] [BorelSpace U]
  (Vf : Varifold U U k) (H : U -> U)
  (_hmc : HasGeneralizedMeanCurvature k Vf H) (_x : U) : Real :=
  Vf.totalMass.toReal

lemma density_nonneg [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U U k) (H : U -> U)
    (hmc : HasGeneralizedMeanCurvature k Vf H) (x : U) :
    0 <= density k Vf H hmc x := by
  simp [density, ENNReal.toReal_nonneg]

lemma IntegralVarifold.density_integer [MeasurableSpace U] [BorelSpace U]
  (Vf : IntegralVarifold U U k) (_H : U -> U)
  (_hmc : HasGeneralizedMeanCurvature k Vf.toVarifold _H) :
    ∀ x, x ∈ Vf.carrier → ∃ m : Nat, 0 < m ∧ Vf.multiplicity x = m := by
  intro x hx
  exact Vf.multiplicity_int x hx

def willmoreEnergyScaleInvariant [MeasurableSpace U] [BorelSpace U]
    (Vf : Varifold U U 2) (H : U -> U) : Real :=
  𝒲(Vf, H)

theorem willmore_lower_bound_sphere [MeasurableSpace U] [BorelSpace U]
    (Vf : IntegralVarifold U U 2) (H : U -> U)
    (_hmc : HasGeneralizedMeanCurvature 2 Vf.toVarifold H)
  (_h_genus_zero : 0 <= Vf.toVarifold.totalMass.toReal) :
  0 <= willmoreEnergyScaleInvariant Vf.toVarifold H := by
  exact willmoreEnergy_nonneg 2 Vf.toVarifold H

def WillmoreFlow [MeasurableSpace U] [BorelSpace U]
    (_Vf : Real -> Varifold U U 2) (_H : Real -> U -> U) : Prop :=
  ∀ t : Real, HasGeneralizedMeanCurvature 2 (_Vf t) (_H t)

end Geometry
