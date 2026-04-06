import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-
# Grassmannian Framework

This module provides a compile-stable framework for Grassmannian objects used
across the Yang-Mills geometry stack.
-/

noncomputable section

/-- The Grassmannian G(V, k) as k-dimensional subspaces of V. -/
def Grassmannian (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (k : ℕ) :=
  { S : Submodule ℝ V // Module.finrank ℝ S = k }

namespace Grassmannian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {k : ℕ}

/-- Canonical orthogonal projection used by downstream geometry files. -/
def proj (S : Grassmannian V k) : V →L[ℝ] V :=
  S.val.starProjection

lemma proj_idempotent (S : Grassmannian V k) :
    (proj S).comp (proj S) = proj S := by
  ext v
  have hmem : proj S v ∈ S.val := by
    change S.val.starProjection v ∈ S.val
    exact S.val.starProjection_apply_mem v
  have hfix : proj S (proj S v) = proj S v := by
    exact (S.val.starProjection_eq_self_iff).2 hmem
  simpa [ContinuousLinearMap.comp_apply] using hfix

lemma proj_mem (S : Grassmannian V k) (v : V) : proj S v ∈ S.val := by
  change S.val.starProjection v ∈ S.val
  exact S.val.starProjection_apply_mem v

/-- Auxiliary distance used for light topological structure. -/
def frobeniusDist (S T : Grassmannian V k) : ℝ :=
  ‖proj S - proj T‖

lemma frobeniusDist_nonneg (S T : Grassmannian V k) : 0 ≤ frobeniusDist S T :=
  by
    exact norm_nonneg _

lemma frobeniusDist_comm (S T : Grassmannian V k) :
    frobeniusDist S T = frobeniusDist T S := by
  simp [frobeniusDist, norm_sub_rev]

lemma frobeniusDist_triangle (S T U : Grassmannian V k) :
    frobeniusDist S U ≤ frobeniusDist S T + frobeniusDist T U := by
  unfold frobeniusDist
  have hdecomp : proj S - proj U = (proj S - proj T) + (proj T - proj U) := by
    ext v
    simp [sub_eq_add_neg, add_assoc, add_left_comm]
  rw [hdecomp]
  exact norm_add_le _ _

instance : PseudoMetricSpace (Grassmannian V k) where
  dist := frobeniusDist
  dist_self S := by simp [frobeniusDist]
  dist_comm S T := frobeniusDist_comm S T
  dist_triangle S T U := frobeniusDist_triangle S T U

instance : MeasurableSpace (Grassmannian V k) :=
  borel (Grassmannian V k)

instance : BorelSpace (Grassmannian V k) :=
  ⟨rfl⟩

end Grassmannian
