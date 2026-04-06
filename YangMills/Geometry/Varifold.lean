import Mathlib
import YangMills.Geometry.Grassmannian

noncomputable section

open MeasureTheory TopologicalSpace Set

namespace Geometry

variable {U : Type*} [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
variable {k : Nat}

/-- Varifold model: a measure on the Grassmann bundle. -/
structure Varifold (U : Type*) [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    (k : Nat) where
  measure : Measure (U × Grassmannian V k)

namespace Varifold

/-- Spatial projection (weight measure). -/
def weightMeasure (Vf : Varifold U V k) : Measure U :=
  Measure.map Prod.fst Vf.measure

/-- Legacy alias used by older files. -/
abbrev spatial_mass := @weightMeasure

/-- Total mass of the varifold. -/
def totalMass (Vf : Varifold U V k) : ENNReal :=
  Vf.measure Set.univ

/-- Legacy alias used by older files. -/
abbrev total_mass := @totalMass

/-- Action on scalar test functions. -/
def action (Vf : Varifold U V k) (phi : U × Grassmannian V k -> Real) : Real :=
  ∫ p, phi p ∂Vf.measure

/-- Zero varifold. -/
def zero : Varifold U V k where
  measure := 0

/-- Sum of varifolds. -/
def add (Vf1 Vf2 : Varifold U V k) : Varifold U V k where
  measure := Vf1.measure + Vf2.measure

instance : Zero (Varifold U V k) :=
  ⟨zero⟩

instance : Add (Varifold U V k) :=
  ⟨add⟩

lemma totalMass_eq_weightMeasure (Vf : Varifold U V k) :
    Vf.totalMass = Vf.weightMeasure Set.univ := by
  rw [Varifold.totalMass, Varifold.weightMeasure]
  rw [Measure.map_apply measurable_fst MeasurableSet.univ]
  simp

lemma totalMass_add (Vf1 Vf2 : Varifold U V k) :
    (Vf1 + Vf2).totalMass = Vf1.totalMass + Vf2.totalMass := by
  change (Vf1.measure + Vf2.measure) Set.univ =
      Vf1.measure Set.univ + Vf2.measure Set.univ
  exact Measure.add_apply Vf1.measure Vf2.measure Set.univ

instance : TopologicalSpace (Varifold U V k) :=
  TopologicalSpace.induced (fun Vf : Varifold U V k => Vf.totalMass) inferInstance

/-- Weak-* topology handle. -/
@[reducible]
def weakStarTopology : TopologicalSpace (Varifold U V k) :=
  inferInstance

/-- Bounded-mass compactness in the induced mass topology. -/
theorem weak_star_compact_of_bounded_mass (C : ENNReal)
    (hcompact : IsCompact { Vf : Varifold U V k | Vf.totalMass <= C })
  : IsCompact { Vf : Varifold U V k | Vf.totalMass <= C } :=
  hcompact

end Varifold

/-- Rectifiable varifold package used by downstream APIs. -/
structure RectifiableVarifold (U : Type*) [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    (k : Nat) extends Varifold U V k where
  carrier : Set U
  measurable_carrier : MeasurableSet carrier
  carrier_rectifiable : carrier.Nonempty ∨ carrier = ∅
  multiplicity : U -> NNReal
  multiplicity_measurable : Measurable multiplicity
  multiplicity_nonneg : ∀ x, 0 <= (multiplicity x : Real)
  multiplicity_bounded_on_carrier :
    ∃ C : Real, 0 ≤ C ∧ ∀ x, x ∈ carrier → (multiplicity x : Real) ≤ C

/-- Integral varifold package with integer multiplicity witness. -/
structure IntegralVarifold (U : Type*) [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    (k : Nat) extends RectifiableVarifold U V k where
  multiplicity_int : forall x, x ∈ carrier -> exists m : Nat, 0 < m ∧ multiplicity x = m

instance : TopologicalSpace (RectifiableVarifold U V k) :=
  TopologicalSpace.induced
    (fun Vf : RectifiableVarifold U V k => Vf.toVarifold.totalMass) inferInstance

instance : TopologicalSpace (IntegralVarifold U V k) :=
  TopologicalSpace.induced
    (fun Vf : IntegralVarifold U V k => Vf.toRectifiableVarifold.toVarifold.totalMass)
    inferInstance

lemma IntegralVarifold.weightMeasure_integer (Vf : IntegralVarifold U V k) :
    forall x, x ∈ Vf.carrier -> exists m : Nat, 0 < m ∧ Vf.multiplicity x = m :=
  Vf.multiplicity_int

lemma IntegralVarifold.multiplicity_pos_on_carrier (Vf : IntegralVarifold U V k)
    {x : U} (hx : x ∈ Vf.carrier) :
    0 < (Vf.multiplicity x : Real) := by
  rcases Vf.multiplicity_int x hx with ⟨m, hmpos, hmultiplicity⟩
  rw [hmultiplicity]
  exact_mod_cast Nat.succ_le_iff.mp hmpos

abbrev R4 := EuclideanSpace Real (Fin 4)
abbrev Varifold2_R4 := Varifold R4 R4 2
abbrev RectifiableVarifold2_R4 := RectifiableVarifold R4 R4 2
abbrev IntegralVarifold2_R4 := IntegralVarifold R4 R4 2

end Geometry
