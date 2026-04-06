import YangMills.Algebra.WillmoreMajorization
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section

open MeasureTheory TopologicalSpace Metric Set Filter
open scoped Real ComplexConjugate Topology

namespace YangMills
namespace UvAsymptotics

open PeterWeyl WillmoreMajorization

variable (N : ℕ)
variable (g_coupling : ℝ)

/-- Exact finite character-expansion plaquette kernel. -/
def ExactPlaquetteKernel (chi_r : ℕ → SUN N → ℂ)
    (d_r : ℕ → ℝ) (beta_r : ℕ → ℝ → ℂ)
    (U : SUN N) (K : ℕ) : ℂ :=
  ∑ r ∈ (Finset.range K), (d_r r : ℂ) * beta_r r g_coupling * chi_r r U

/-- Finite-sum norm control by the triangle inequality. -/
lemma analytic_finiteness_coupling
    (chi_r : ℕ → SUN N → ℂ) (d_r : ℕ → ℝ)
    (beta_r : ℕ → ℝ → ℂ) (U : SUN N) (K : ℕ) :
  ‖ExactPlaquetteKernel N g_coupling chi_r d_r beta_r U K‖ ≤ 
  ∑ r ∈ (Finset.range K), ‖(d_r r : ℂ) * beta_r r g_coupling * chi_r r U‖ := by
  dsimp [ExactPlaquetteKernel]
  exact norm_sum_le (Finset.range K) (fun r => (d_r r : ℂ) * beta_r r g_coupling * chi_r r U)

/-- Uniform finite-mode bound under a per-mode amplitude hypothesis. -/
lemma analytic_finiteness_coupling_uniform_bound
    (chi_r : ℕ → SUN N → ℂ) (d_r : ℕ → ℝ) (beta_r : ℕ → ℝ → ℂ)
    (U : SUN N) (K : ℕ) (B : ℝ)
    (hB : ∀ r ∈ Finset.range K, ‖(d_r r : ℂ) * beta_r r g_coupling * chi_r r U‖ ≤ B) :
    ‖ExactPlaquetteKernel N g_coupling chi_r d_r beta_r U K‖ ≤ (K : ℝ) * B := by
  have htriangle := analytic_finiteness_coupling N g_coupling chi_r d_r beta_r U K
  refine le_trans htriangle ?_
  calc
    ∑ r ∈ Finset.range K, ‖(d_r r : ℂ) * beta_r r g_coupling * chi_r r U‖
      ≤ ∑ r ∈ Finset.range K, B := by
          exact Finset.sum_le_sum (fun r hr => hB r hr)
        _ = ((Finset.range K).card : ℝ) * B := by
          simp [Finset.sum_const]
        _ = (K : ℝ) * B := by
          simp

/-- Finite UV truncation always admits an explicit nonnegative norm certificate. -/
theorem uv_asymptotic_finiteness_certificate
    (chi_r : ℕ → SUN N → ℂ) (d_r : ℕ → ℝ) (beta_r : ℕ → ℝ → ℂ)
    (U : SUN N) (K : ℕ) (B : ℝ)
    (hBnonneg : 0 ≤ B)
    (hB : ∀ r ∈ Finset.range K, ‖(d_r r : ℂ) * beta_r r g_coupling * chi_r r U‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖ExactPlaquetteKernel N g_coupling chi_r d_r beta_r U K‖ ≤ C := by
  refine ⟨(K : ℝ) * B, mul_nonneg (Nat.cast_nonneg K) hBnonneg, ?_⟩
  exact analytic_finiteness_coupling_uniform_bound N g_coupling chi_r d_r beta_r U K B hB

end UvAsymptotics
end YangMills
