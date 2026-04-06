import YangMills.Geometry.Decomposition
import YangMills.Geometry.IntegralVarifold

noncomputable section

open MeasureTheory TopologicalSpace Set
open Grassmannian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {U : Type*} [TopologicalSpace U]
variable (k : ℕ)

namespace Geometry

/-- Rigorous normal-orthogonality constraint for the generalized mean-curvature field. -/
structure NormalOrthogonality [MeasurableSpace U] [BorelSpace U]
  (Vf : IntegralVarifold U V k)
  (decomp : VariationDecomposition k Vf.toVarifold) where
  -- Orthogonality of the projected curvature field.
  is_normal : ∀ x ∈ Vf.carrier, ∀ S : Grassmannian V k,
    -- Projection to any tangent k-plane vanishes.
    proj S (decomp.H x) = 0

lemma NormalOrthogonality.proj_eq_zero
    [MeasurableSpace U] [BorelSpace U]
  {Vf : IntegralVarifold U V k}
    {decomp : VariationDecomposition k Vf.toVarifold}
    (horth : NormalOrthogonality k Vf decomp)
    {x : U} (hx : x ∈ Vf.carrier) (S : Grassmannian V k) :
    proj S (decomp.H x) = 0 :=
  horth.is_normal x hx S

lemma NormalOrthogonality.proj_eq_zero_of_mem
    [MeasurableSpace U] [BorelSpace U]
  {Vf : IntegralVarifold U V k}
    {decomp : VariationDecomposition k Vf.toVarifold}
    (horth : NormalOrthogonality k Vf decomp) :
    ∀ x,
      x ∈ Vf.carrier →
      ∀ S : Grassmannian V k, proj S (decomp.H x) = 0 := by
  intro x hx S
  exact horth.is_normal x hx S

end Geometry
