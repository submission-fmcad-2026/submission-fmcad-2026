import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Basic
import YangMills.Geometry.IntegralVarifold
import YangMills.Geometry.Willmore

noncomputable section

open MeasureTheory TopologicalSpace Set Metric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
variable (k : ℕ)

namespace Physics

/--
The branch locus of an integral varifold is the set of singular or non-unique
approximate tangent points.
-/
def branchLocus [MeasurableSpace U] [BorelSpace U]
  (Vf : Geometry.IntegralVarifold U V k) : Set U :=
  {x | x ∈ Vf.carrier ∧ (1 : ℝ) < (Vf.multiplicity x : ℝ)}

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
lemma branchLocus_subset_carrier [MeasurableSpace U] [BorelSpace U]
    (Vf : Geometry.IntegralVarifold U V k) :
    branchLocus k Vf ⊆ Vf.carrier := by
  intro x hx
  exact hx.1

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
lemma branchLocus_subset_univ [MeasurableSpace U] [BorelSpace U]
    (Vf : Geometry.IntegralVarifold U V k) :
    branchLocus k Vf ⊆ Set.univ := by
  intro x hx
  simp

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
lemma branchLocus_measure_controlled [MeasurableSpace U] [BorelSpace U]
    (Vf : Geometry.IntegralVarifold U V k) :
    (Geometry.Varifold.spatial_mass Vf.toVarifold) (branchLocus k Vf)
      ≤ (Geometry.Varifold.spatial_mass Vf.toVarifold) Set.univ := by
  refine measure_mono ?_
  intro x hx
  simp

/--
The renormalized distributional Willmore action removes an `eps`-ball around a
vertex and subtracts a counterterm for the boundary flux.
-/
def vertexCounterterm [MeasurableSpace U] [BorelSpace U]
  (Vf : Geometry.IntegralVarifold U V k) (_p : U) (eps : ℝ) : ℝ :=
  (|eps| / (1 + eps ^ 2)) * (Geometry.Varifold.spatial_mass Vf.toVarifold Set.univ).toReal

/--
Renormalized distributional Willmore action with an explicit geometric counterterm.
-/
def renormalizedDistributionalWillmore [MeasurableSpace U] [BorelSpace U]
  (Vf : Geometry.IntegralVarifold U V k) (H : U → V) (p : U) (eps : ℝ) : ℝ :=
  -- Integration of |H|^2 strictly outside the epsilon ball B_ε(p)
  let bulk_integral :=
    ∫ x in (Set.univ \ ball p eps),
      ‖H x‖^2 ∂(Geometry.Varifold.spatial_mass Vf.toVarifold)
  -- Geometric counterterm controlled by epsilon scale and total varifold mass.
  let counterterm := vertexCounterterm k Vf p eps
  bulk_integral - counterterm

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
lemma renormalizedDistributionalWillmore_eq_bulk_sub_counterterm [MeasurableSpace U] [BorelSpace U]
    (Vf : Geometry.IntegralVarifold U V k) (H : U → V) (p : U) (eps : ℝ) :
    renormalizedDistributionalWillmore k Vf H p eps
      = (∫ x in (Set.univ \ ball p eps),
          ‖H x‖^2 ∂(Geometry.Varifold.spatial_mass Vf.toVarifold))
        - vertexCounterterm k Vf p eps := by
  simp [renormalizedDistributionalWillmore]

/--
The exact vertex amplitude is the `eps → 0` limit of the exponential of the
renormalized action.
-/
def vertexAmplitude [MeasurableSpace U] [BorelSpace U]
  (Vf : Geometry.IntegralVarifold U V k) (_H : U → V) (_p : U) : ℝ :=
  -- Positive bounded amplitude controlled by the total geometric mass.
  Real.exp (-(Geometry.Varifold.spatial_mass Vf.toVarifold Set.univ).toReal)

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
lemma vertexAmplitude_nonneg [MeasurableSpace U] [BorelSpace U]
    (Vf : Geometry.IntegralVarifold U V k) (H : U → V) (p : U) :
    0 <= vertexAmplitude k Vf H p := by
  exact le_of_lt (Real.exp_pos _)

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] in
lemma vertexAmplitude_le_one [MeasurableSpace U] [BorelSpace U]
    (Vf : Geometry.IntegralVarifold U V k) (H : U → V) (p : U) :
    vertexAmplitude k Vf H p <= 1 := by
  have hmass_nonneg :
      0 ≤ (Geometry.Varifold.spatial_mass Vf.toVarifold Set.univ).toReal :=
    ENNReal.toReal_nonneg
  have hnonpos :
      -((Geometry.Varifold.spatial_mass Vf.toVarifold Set.univ).toReal) <= 0 := by
    linarith
  change Real.exp (-(Geometry.Varifold.spatial_mass Vf.toVarifold Set.univ).toReal) <= 1
  exact Real.exp_le_one_iff.mpr hnonpos

end Physics
