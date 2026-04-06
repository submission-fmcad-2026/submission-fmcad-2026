import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.Set.Countable

noncomputable section

open MeasureTheory TopologicalSpace Set Metric

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

namespace Geometry

/--
A set `M` is countably `k`-rectifiable if, up to a Hausdorff-null set, it is
covered by countably many Lipschitz images of subsets of a `k`-dimensional
inner product space.
-/
def IsCountablyRectifiable (k : ℝ) (M : Set V) : Prop :=
  ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : FiniteDimensional ℝ E)
    (_ : MeasurableSpace E) (_ : BorelSpace E)
    (_ : Module.finrank ℝ E = k),
  ∃ (A : ℕ → Set E) (f : ℕ → E → V) (L : ℕ → ℝ),
    (∀ i, LipschitzWith (Real.toNNReal (L i)) (f i)) ∧
    (Measure.hausdorffMeasure k (M \ ⋃ i, f i '' (A i)) = 0)

end Geometry
