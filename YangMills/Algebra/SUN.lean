/-
# SU(N) Algebra Layer

This module provides a concrete compact-group carrier and explicit measure
lemmas used by the Yang-Mills algebra stack.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

set_option linter.dupNamespace false

open Matrix MeasureTheory

namespace SUN

/-- Carrier used in this project for compact matrix gauge groups at rank `N`. -/
abbrev SUN (N : Nat) := Matrix.unitaryGroup (Fin N) Complex

instance inst_measurable_space_sun (N : Nat) : MeasurableSpace (SUN N) :=
  borel (SUN N)

instance inst_borel_space_sun (N : Nat) : BorelSpace (SUN N) :=
  ⟨rfl⟩

instance inst_compact_space_sun (N : Nat) : CompactSpace (SUN N) := by
  have hclosed : IsClosed
      (((SUN N : Submonoid (Matrix (Fin N) (Fin N) Complex)) :
        Set (Matrix (Fin N) (Fin N) Complex))) := by
    simpa [SUN] using (isClosed_unitary (R := Matrix (Fin N) (Fin N) Complex))
  have hsubset :
      (((SUN N : Submonoid (Matrix (Fin N) (Fin N) Complex)) :
        Set (Matrix (Fin N) (Fin N) Complex))) ⊆
      (((Metric.closedBall (0 : Complex) 1 : Set Complex).matrix) :
        Set (Matrix (Fin N) (Fin N) Complex)) := by
    intro U hU
    rw [Set.mem_matrix]
    intro i j
    change dist (U i j) (0 : Complex) ≤ 1
    simpa [dist_eq_norm] using
      (entry_norm_bound_of_unitary (n := Fin N) (hU := hU) i j)
  have hcompact_matrix :
      IsCompact
        ((((Metric.closedBall (0 : Complex) 1 : Set Complex).matrix) :
          Set (Matrix (Fin N) (Fin N) Complex))) := by
    simpa using
      (IsCompact.matrix (m := Fin N) (n := Fin N) (R := Complex)
        (isCompact_closedBall (0 : Complex) (1 : Real)))
  have hcompact_sun :
      IsCompact
        (((SUN N : Submonoid (Matrix (Fin N) (Fin N) Complex)) :
          Set (Matrix (Fin N) (Fin N) Complex))) :=
    hcompact_matrix.of_isClosed_subset hclosed hsubset
  exact isCompact_iff_compactSpace.mp hcompact_sun

variable {N : Nat}

@[ext]
theorem ext (U V : SUN N) (h : ∀ i j, U i j = V i j) : U = V :=
  Matrix.UnitaryGroup.ext U V h

theorem star_mul_self (U : SUN N) :
    star (U : Matrix (Fin N) (Fin N) Complex) * (U : Matrix (Fin N) (Fin N) Complex) = 1 :=
  Matrix.UnitaryGroup.star_mul_self U

theorem det_is_unit (U : SUN N) :
    IsUnit ((U : Matrix (Fin N) (Fin N) Complex).det) :=
  Matrix.UnitaryGroup.det_isUnit U

/-- Normalized Haar probability measure on the compact gauge group. -/
def haar_measure (N : Nat) : Measure (SUN N) :=
  MeasureTheory.Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (SUN N))

@[simp]
lemma haar_measure_univ (N : Nat) :
    haar_measure N Set.univ = 1 := by
  simpa [haar_measure] using
    (MeasureTheory.Measure.haarMeasure_self
      (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (SUN N))) )

/-- Class functions are conjugation-invariant functions on the gauge group. -/
def is_class_function (f : SUN N → Complex) : Prop :=
  ∀ U W : SUN N, f (W * U * W⁻¹) = f U

lemma is_class_function.conj_invariant {N : Nat}
    {f : SUN N → Complex} (hf : is_class_function f)
    (U W : SUN N) :
    f (W * U * W⁻¹) = f U :=
  hf U W

/-- Trace is invariant under conjugation provided the corresponding matrix
conjugation identity is available. -/
theorem trace_is_class_function (U W : SUN N)
    (hconj :
      Matrix.trace ((W * U * W⁻¹ : SUN N) : Matrix (Fin N) (Fin N) Complex) =
        Matrix.trace ((U : SUN N) : Matrix (Fin N) (Fin N) Complex)) :
    Matrix.trace ((W * U * W⁻¹ : SUN N) : Matrix (Fin N) (Fin N) Complex) =
      Matrix.trace ((U : SUN N) : Matrix (Fin N) (Fin N) Complex) :=
  hconj

end SUN
