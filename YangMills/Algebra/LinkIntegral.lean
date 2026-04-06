/-
# Link Integral Algebra Layer

This module keeps a compact API for link-integral constructions while exposing
quantitative positivity and truncation-control lemmas used downstream.
-/

import YangMills.Algebra.PeterWeyl

noncomputable section

namespace YangMills
namespace LinkIntegral

variable (N : Nat)

/-- Link-integrand model built from plaquette Boltzmann weights. -/
def LinkIntegrand (g : Real) (U : PeterWeyl.SUN N) : Real :=
  PeterWeyl.PlaquetteWeight N g U

/-- Baseline positivity lemma: link integrand is strictly positive pointwise. -/
theorem link_integrand_pos (g : Real) (U : PeterWeyl.SUN N) :
    0 < LinkIntegrand N g U :=
  PeterWeyl.plaquette_weight_pos N g U

theorem link_integral_ready (g : Real) (U : PeterWeyl.SUN N) :
    0 < LinkIntegrand N g U :=
  link_integrand_pos N g U

/-- Finite Fourier-Weyl truncation as seen from the link-integral layer. -/
def LinkFourierTruncation (g : Real) (labels : Finset (SUN.DominantWeight N))
    (U : PeterWeyl.SUN N) : Real :=
  PeterWeyl.FourierWeylTruncation N g labels U

lemma linkFourierTruncation_nonneg (g : Real) (labels : Finset (SUN.DominantWeight N))
    (U : PeterWeyl.SUN N) :
    0 <= LinkFourierTruncation N g labels U :=
  PeterWeyl.fourierWeylTruncation_nonneg N g labels U

/-- Card-control identity exported for downstream majorization estimates. -/
theorem link_truncation_control_by_card (g : Real)
    (labels : Finset (SUN.DominantWeight N)) (U : PeterWeyl.SUN N) :
  LinkFourierTruncation N g labels U <=
      PeterWeyl.FourierDimensionMass N labels * LinkIntegrand N g U := by
  unfold LinkFourierTruncation LinkIntegrand
  simpa using PeterWeyl.truncation_control_by_card N g labels U

/-- Finite absolute-control bridge for link-integral truncations. -/
theorem link_finite_absolute_convergence_bridge (g : Real)
    (labels : Finset (SUN.DominantWeight N)) (U : PeterWeyl.SUN N) :
    |LinkFourierTruncation N g labels U|
      <= PeterWeyl.FourierDimensionMass N labels * LinkIntegrand N g U := by
  unfold LinkFourierTruncation LinkIntegrand
  simpa using PeterWeyl.finite_absolute_convergence_bridge N g labels U

/-- Selection decomposition: every finite truncation splits into selected and complement sectors. -/
theorem link_nality_selection_split (g : Real)
    (labels : Finset (SUN.DominantWeight N))
    (sector : SUN.DominantWeight N → Prop) [DecidablePred sector]
    (U : PeterWeyl.SUN N) :
    LinkFourierTruncation N g labels U
      = LinkFourierTruncation N g (labels.filter sector) U
          + LinkFourierTruncation N g (labels.filter (fun lam => ¬ sector lam)) U := by
  unfold LinkFourierTruncation
  simpa using
    (Finset.sum_filter_add_sum_filter_not
      (s := labels)
      (p := sector)
      (f := fun lam => PeterWeyl.FourierWeylCoefficient N g lam U)).symm

/-- Closure bound on any selected sector, controlled by the ambient cardinality. -/
theorem link_nality_closure_bound (g : Real)
    (labels : Finset (SUN.DominantWeight N))
    (sector : SUN.DominantWeight N → Prop) [DecidablePred sector]
    (U : PeterWeyl.SUN N) :
    |LinkFourierTruncation N g (labels.filter sector) U|
      <= PeterWeyl.FourierDimensionMass N labels * LinkIntegrand N g U := by
  have hbridge := link_finite_absolute_convergence_bridge N g (labels.filter sector) U
  have hcard :
      PeterWeyl.FourierDimensionMass N (labels.filter sector) <=
        PeterWeyl.FourierDimensionMass N labels :=
    PeterWeyl.fourierDimensionMass_filter_le N labels sector
  have hnonneg : 0 <= LinkIntegrand N g U := by
    exact le_of_lt (link_integral_ready N g U)
  have hmul :
      PeterWeyl.FourierDimensionMass N (labels.filter sector) * LinkIntegrand N g U
        <= PeterWeyl.FourierDimensionMass N labels * LinkIntegrand N g U :=
    mul_le_mul_of_nonneg_right hcard hnonneg
  exact le_trans hbridge hmul

/-- Triangle bound for the selected/complement decomposition. -/
theorem link_nality_selection_abs_bound (g : Real)
    (labels : Finset (SUN.DominantWeight N))
    (sector : SUN.DominantWeight N → Prop) [DecidablePred sector]
    (U : PeterWeyl.SUN N) :
    |LinkFourierTruncation N g labels U|
      <= |LinkFourierTruncation N g (labels.filter sector) U|
        + |LinkFourierTruncation N g (labels.filter (fun lam => ¬ sector lam)) U| := by
  have hsplit := link_nality_selection_split N g labels sector U
  rw [hsplit]
  simpa [Real.norm_eq_abs] using
    (norm_add_le
      (LinkFourierTruncation N g (labels.filter sector) U)
      (LinkFourierTruncation N g (labels.filter (fun lam => ¬ sector lam)) U))

end LinkIntegral
end YangMills
