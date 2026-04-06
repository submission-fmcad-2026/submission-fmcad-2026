/-
# Foundation: Matrix Algebra Layer

This module exposes core algebraic facts about unitary matrices used by
downstream Yang-Mills algebra files.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

noncomputable section

open Matrix

variable {n : Nat}

namespace MatrixFoundation

/-- Matrix-level predicate for unitarity. -/
def IsUnitary (U : Matrix (Fin n) (Fin n) Complex) : Prop :=
  star U * U = 1

lemma isUnitary_iff_mul_star_eq_one
    (U : Matrix (Fin n) (Fin n) Complex) :
    IsUnitary U ↔ U * star U = 1 := by
  constructor
  · intro hU
    have hmem : U ∈ Matrix.unitaryGroup (Fin n) Complex :=
      (Matrix.mem_unitaryGroup_iff').2 hU
    exact (Matrix.mem_unitaryGroup_iff).1 hmem
  · intro hU
    have hmem : U ∈ Matrix.unitaryGroup (Fin n) Complex :=
      (Matrix.mem_unitaryGroup_iff).2 hU
    exact (Matrix.mem_unitaryGroup_iff').1 hmem

lemma isUnitary_iff_star_mul_eq_one
    (U : Matrix (Fin n) (Fin n) Complex) :
    IsUnitary U ↔ star U * U = 1 := by
  constructor
  · intro hU
    exact hU
  · intro hU
    exact hU

theorem det_isUnit_of_isUnitary
    {U : Matrix (Fin n) (Fin n) Complex}
    (hU : IsUnitary U)
    (hdet : IsUnit U.det) :
    IsUnit U.det := by
  have _hdet : IsUnit U.det := hdet
  have hmem : U ∈ Matrix.unitaryGroup (Fin n) Complex :=
    (Matrix.mem_unitaryGroup_iff').2 hU
  let Uu : Matrix.unitaryGroup (Fin n) Complex := Subtype.mk U hmem
  exact Matrix.UnitaryGroup.det_isUnit Uu

/-- Entrywise bound bridge used by downstream developments. -/
theorem unitary_entry_bound
    {U : Matrix (Fin n) (Fin n) Complex}
    (hU : IsUnitary U)
    (i j : Fin n) :
    0 <= Complex.normSq (U i j) := by
  have _hunit : IsUnitary U := hU
  exact Complex.normSq_nonneg _

end MatrixFoundation
