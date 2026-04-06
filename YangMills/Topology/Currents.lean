import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-
# Currents Layer

This module introduces a graded formalization of differential forms and
currents based on compactly supported test forms.
-/

noncomputable section

namespace Topology

/-- Degree-`k` differential forms on `U` with values in `V`. -/
abbrev DifferentialForm (U : Type*) [TopologicalSpace U] (V : Type*) (_k : ℕ) : Type _ :=
  U → V

namespace DifferentialForm

variable {U : Type*} [TopologicalSpace U]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {k : ℕ}

/-- View a differential form as its underlying function. -/
def form (ω : DifferentialForm U V k) : U → V :=
  ω

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
@[simp] lemma form_apply (ω : DifferentialForm U V k) (x : U) :
    ω.form x = ω x :=
  rfl

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
@[ext] lemma ext {ω₁ ω₂ : DifferentialForm U V k}
    (h : ∀ x : U, ω₁ x = ω₂ x) : ω₁ = ω₂ :=
  funext h

omit [NormedSpace ℝ V] in
@[simp] lemma add_form_apply (ω₁ ω₂ : DifferentialForm U V k) (x : U) :
    (ω₁ + ω₂).form x = ω₁.form x + ω₂.form x :=
  rfl

omit [NormedSpace ℝ V] in
@[simp] lemma neg_form_apply (ω : DifferentialForm U V k) (x : U) :
    (-ω).form x = -ω.form x :=
  rfl

omit [NormedSpace ℝ V] in
@[simp] lemma sub_form_apply (ω₁ ω₂ : DifferentialForm U V k) (x : U) :
    (ω₁ - ω₂).form x = ω₁.form x - ω₂.form x :=
  rfl

@[simp] lemma smul_form_apply (c : ℝ) (ω : DifferentialForm U V k) (x : U) :
    (c • ω).form x = c • ω.form x :=
  rfl

end DifferentialForm

/-- Compactly supported degree-`k` forms as a submodule of all forms. -/
def compactlySupportedForms (U : Type*) [TopologicalSpace U]
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) :
    Submodule ℝ (DifferentialForm U V k) where
  carrier := { ω | HasCompactSupport ω }
  zero_mem' := by
    simpa using (HasCompactSupport.zero : HasCompactSupport (0 : DifferentialForm U V k))
  add_mem' := by
    intro ω₁ ω₂ h₁ h₂
    simpa using HasCompactSupport.add h₁ h₂
  smul_mem' := by
    intro c ω hω
    simpa [Pi.smul_apply] using
      (HasCompactSupport.smul_left (f := fun _ : U => c) hω)

/-- Compactly supported test forms of degree `k`. -/
abbrev TestForm (U : Type*) [TopologicalSpace U]
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) : Type _ :=
  compactlySupportedForms U V k

/--
Abstract exterior differential package:

* `d` raises degree by one;
* `d` is linear;
* `d` preserves compact support on test forms;
* `d^2 = 0`.
-/
class ExteriorDifferential (U : Type*) [TopologicalSpace U]
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  d : {k : ℕ} → DifferentialForm U V k → DifferentialForm U V (k + 1)
  d_add : ∀ {k : ℕ} (ω₁ ω₂ : DifferentialForm U V k),
    d (ω₁ + ω₂) = d ω₁ + d ω₂
  d_smul : ∀ {k : ℕ} (c : ℝ) (ω : DifferentialForm U V k),
    d (c • ω) = c • d ω
  d_squared_zero : ∀ {k : ℕ} (ω : DifferentialForm U V k), d (d ω) = 0
  d_hasCompactSupport : ∀ {k : ℕ} {ω : DifferentialForm U V k},
    HasCompactSupport ω → HasCompactSupport (d ω)

namespace DifferentialForm

variable {U : Type*} [TopologicalSpace U]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [ExteriorDifferential U V]

/-- Exterior derivative on all forms. -/
def exteriorDerivative {k : ℕ} (ω : DifferentialForm U V k) : DifferentialForm U V (k + 1) :=
  ExteriorDifferential.d ω

@[simp] lemma exteriorDerivative_add {k : ℕ} (ω₁ ω₂ : DifferentialForm U V k) :
    exteriorDerivative (ω₁ + ω₂) = exteriorDerivative ω₁ + exteriorDerivative ω₂ :=
  ExteriorDifferential.d_add ω₁ ω₂

@[simp] lemma exteriorDerivative_smul {k : ℕ} (c : ℝ) (ω : DifferentialForm U V k) :
    exteriorDerivative (c • ω) = c • exteriorDerivative ω :=
  ExteriorDifferential.d_smul c ω

@[simp] lemma exteriorDerivative_squared_zero {k : ℕ} (ω : DifferentialForm U V k) :
    exteriorDerivative (exteriorDerivative ω) = 0 :=
  ExteriorDifferential.d_squared_zero ω

/-- Exterior derivative restricted to compactly supported test forms. -/
def exteriorDerivativeOnTestForms (k : ℕ) :
    TestForm U V k →ₗ[ℝ] TestForm U V (k + 1) where
  toFun ω :=
    ⟨exteriorDerivative ω.1,
      ExteriorDifferential.d_hasCompactSupport (ω := ω.1) ω.2⟩
  map_add' ω₁ ω₂ := by
    apply Subtype.ext
    change exteriorDerivative (ω₁.1 + ω₂.1) = exteriorDerivative ω₁.1 + exteriorDerivative ω₂.1
    exact exteriorDerivative_add (ω₁ := ω₁.1) (ω₂ := ω₂.1)
  map_smul' c ω := by
    apply Subtype.ext
    change exteriorDerivative (c • ω.1) = c • exteriorDerivative ω.1
    exact exteriorDerivative_smul (c := c) (ω := ω.1)

@[simp] lemma exteriorDerivativeOnTestForms_apply (k : ℕ)
    (ω : TestForm U V k) :
    (exteriorDerivativeOnTestForms (U := U) (V := V) k ω).1 = exteriorDerivative ω.1 :=
  rfl

@[simp] lemma exteriorDerivativeOnTestForms_squared_zero (k : ℕ)
    (ω : TestForm U V k) :
    exteriorDerivativeOnTestForms (U := U) (V := V) (k + 1)
      (exteriorDerivativeOnTestForms (U := U) (V := V) k ω) = 0 := by
  apply Subtype.ext
  change exteriorDerivative (exteriorDerivative ω.1) = 0
  exact exteriorDerivative_squared_zero (ω := ω.1)

end DifferentialForm

/-- A degree-`k` current is a linear functional on compactly supported degree-`k` forms. -/
structure GeneralCurrent (U : Type*) [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (k : ℕ) where
  toLinearMap : TestForm U V k →ₗ[ℝ] ℝ

/-- Alias emphasizing dual-space semantics. -/
abbrev Current (U : Type*) [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (k : ℕ) :=
  GeneralCurrent U V k

namespace GeneralCurrent

variable {U : Type*} [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {k : ℕ}

def action (T : GeneralCurrent U V k) : TestForm U V k → ℝ :=
  T.toLinearMap

@[simp] lemma action_apply (T : GeneralCurrent U V k) (ω : TestForm U V k) :
    T.action ω = T.toLinearMap ω :=
  rfl

instance : CoeFun (GeneralCurrent U V k) (fun _ => TestForm U V k → ℝ) where
  coe T := T.action

instance : Zero (GeneralCurrent U V k) where
  zero := ⟨0⟩

instance : Add (GeneralCurrent U V k) where
  add T₁ T₂ := ⟨T₁.toLinearMap + T₂.toLinearMap⟩

instance : SMul ℝ (GeneralCurrent U V k) where
  smul c T := ⟨c • T.toLinearMap⟩

@[simp] lemma zero_toLinearMap :
    (0 : GeneralCurrent U V k).toLinearMap = 0 :=
  rfl

@[simp] lemma zero_toLinearMap_apply (ω : TestForm U V k) :
    (0 : GeneralCurrent U V k).toLinearMap ω = 0 :=
  rfl

@[simp] lemma zero_action_apply (ω : TestForm U V k) :
    (0 : GeneralCurrent U V k).action ω = 0 :=
  rfl

@[simp] lemma zero_apply (ω : TestForm U V k) :
    (0 : GeneralCurrent U V k) ω = 0 :=
  rfl

@[simp] lemma action_add (T : GeneralCurrent U V k) (ω₁ ω₂ : TestForm U V k) :
    T.action (ω₁ + ω₂) = T.action ω₁ + T.action ω₂ :=
  T.toLinearMap.map_add ω₁ ω₂

@[simp] lemma action_smul (T : GeneralCurrent U V k) (c : ℝ) (ω : TestForm U V k) :
    T.action (c • ω) = c * T.action ω := by
  change T.toLinearMap (c • ω) = c * T.toLinearMap ω
  calc
    T.toLinearMap (c • ω) = c • T.toLinearMap ω := T.toLinearMap.map_smulₛₗ c ω
    _ = c * T.toLinearMap ω := by simp [smul_eq_mul]

@[simp] lemma action_zero (T : GeneralCurrent U V k) :
    T.action 0 = 0 :=
  T.toLinearMap.map_zero

@[ext] lemma ext {T₁ T₂ : GeneralCurrent U V k}
    (h : ∀ ω : TestForm U V k, T₁.action ω = T₂.action ω) : T₁ = T₂ := by
  cases T₁ with
  | mk L₁ =>
      cases T₂ with
      | mk L₂ =>
        have hL : L₁ = L₂ := by
          ext ω
          exact h ω
        cases hL
        rfl

end GeneralCurrent

/--
Abstract norm model on test forms used to define the dual mass norm of currents.
This is a fallback when no canonical norm instance is available on `TestForm`.
-/
class CurrentNorm (U : Type*) [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] where
  norm : {k : ℕ} → TestForm U V k → ℝ
  norm_nonneg : ∀ {k : ℕ} (ω : TestForm U V k), 0 ≤ norm ω
  norm_zero : ∀ {k : ℕ}, norm (0 : TestForm U V k) = 0
  action_unitBall_bddAbove :
    ∀ {k : ℕ} (T : GeneralCurrent U V k),
      BddAbove { r : ℝ | ∃ ω : TestForm U V k, norm ω ≤ 1 ∧ r = ‖T.action ω‖ }

section Boundary

variable {U : Type*} [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable [ExteriorDifferential U V]

/-- Boundary operator by duality: `(boundary T)(ω) = T(dω)`. -/
def boundaryOperator : (k : ℕ) → GeneralCurrent U V k → GeneralCurrent U V (k - 1)
  | 0, _ => 0
  | k + 1, T =>
      ⟨T.toLinearMap.comp (DifferentialForm.exteriorDerivativeOnTestForms (U := U) (V := V) k)⟩

lemma boundaryOperator_zero (k : ℕ) :
    boundaryOperator (U := U) (V := V) k (0 : GeneralCurrent U V k) = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
    apply GeneralCurrent.ext
    intro ω
    change (0 : ℝ) = ((0 : TestForm U V (k + 1 - 1) →ₗ[ℝ] ℝ) ω)
    have hzero : ((0 : TestForm U V (k + 1 - 1) →ₗ[ℝ] ℝ) ω) = 0 := rfl
    exact hzero.symm

/-- Boundary squared is zero, induced by `d^2 = 0` on test forms. -/
lemma boundary_squared_zero (k : ℕ) (T : GeneralCurrent U V k) :
    boundaryOperator (U := U) (V := V) (k - 1)
      (boundaryOperator (U := U) (V := V) k T) = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero =>
      simp [boundaryOperator]
    | succ k =>
      apply GeneralCurrent.ext
      intro ω
      have hdd :
          DifferentialForm.exteriorDerivativeOnTestForms (U := U) (V := V) (k + 1)
            (DifferentialForm.exteriorDerivativeOnTestForms (U := U) (V := V) k ω) = 0 :=
        DifferentialForm.exteriorDerivativeOnTestForms_squared_zero (U := U) (V := V) k ω
      change
        T.toLinearMap
            (DifferentialForm.exteriorDerivativeOnTestForms (U := U) (V := V) (k + 1)
              (DifferentialForm.exteriorDerivativeOnTestForms (U := U) (V := V) k ω)) = 0
      rw [hdd]
      simp

variable [CurrentNorm U V]

/--
Mass norm (dual GMT model): supremum over the unit ball of compactly supported
test forms.
-/
def massNorm (k : ℕ) (T : GeneralCurrent U V k) : ℝ :=
  sSup { r : ℝ | ∃ ω : TestForm U V k,
    CurrentNorm.norm (U := U) (V := V) (k := k) ω ≤ 1 ∧ r = ‖T.action ω‖ }

/-- Flat norm model: mass plus boundary mass. -/
def flatNorm (k : ℕ) (T : GeneralCurrent U V k) : ℝ :=
  massNorm (U := U) (V := V) k T
    + massNorm (U := U) (V := V) (k - 1) (boundaryOperator (U := U) (V := V) k T)

omit [ExteriorDifferential U V] in
lemma massNorm_nonneg (k : ℕ) (T : GeneralCurrent U V k) :
    0 ≤ massNorm (U := U) (V := V) k T := by
  unfold massNorm
  have hzero_mem :
      (0 : ℝ) ∈ { r : ℝ | ∃ ω : TestForm U V k,
        CurrentNorm.norm (U := U) (V := V) (k := k) ω ≤ 1 ∧ r = ‖T.action ω‖ } := by
    refine ⟨0, ?_, ?_⟩
    · have h0 : CurrentNorm.norm (U := U) (V := V) (k := k) (0 : TestForm U V k) = 0 :=
        CurrentNorm.norm_zero (U := U) (V := V) (k := k)
      rw [h0]
      norm_num
    · simp
  exact le_csSup
    (CurrentNorm.action_unitBall_bddAbove (U := U) (V := V) T)
    hzero_mem

omit [ExteriorDifferential U V] in
lemma massNorm_zero (k : ℕ) :
    massNorm (U := U) (V := V) k (0 : GeneralCurrent U V k) = 0 := by
  unfold massNorm
  let A : Set ℝ := { r : ℝ | ∃ ω : TestForm U V k,
    CurrentNorm.norm (U := U) (V := V) (k := k) ω ≤ 1 ∧
      r = ‖(0 : GeneralCurrent U V k).action ω‖ }
  change sSup A = 0
  have hA : A = {0} := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨ω, _hω, hr⟩
      rw [hr]
      simp
    · intro hr
      rcases hr with rfl
      refine ⟨0, ?_, ?_⟩
      · have h0 : CurrentNorm.norm (U := U) (V := V) (k := k) (0 : TestForm U V k) = 0 :=
          CurrentNorm.norm_zero (U := U) (V := V) (k := k)
        rw [h0]
        norm_num
      · simp
  rw [hA]
  simp

lemma massNorm_boundary_eq_zero (k : ℕ) (T : GeneralCurrent U V k) :
    boundaryOperator (U := U) (V := V) k T = 0 →
    massNorm (U := U) (V := V) (k - 1) (boundaryOperator (U := U) (V := V) k T) = 0 := by
  intro hbd
  simpa [hbd] using (massNorm_zero (U := U) (V := V) (k := k - 1))

lemma flatNorm_nonneg (k : ℕ) (T : GeneralCurrent U V k) :
    0 ≤ flatNorm (U := U) (V := V) k T := by
  unfold flatNorm
  exact add_nonneg
    (massNorm_nonneg (U := U) (V := V) k T)
    (massNorm_nonneg (U := U) (V := V) (k - 1) (boundaryOperator (U := U) (V := V) k T))

lemma flatNorm_zero (k : ℕ) :
    flatNorm (U := U) (V := V) k (0 : GeneralCurrent U V k) = 0 := by
  simp [flatNorm, massNorm_zero, boundaryOperator_zero]

lemma flatNorm_eq_massNorm (k : ℕ) (T : GeneralCurrent U V k) :
    boundaryOperator (U := U) (V := V) k T = 0 →
    flatNorm (U := U) (V := V) k T = massNorm (U := U) (V := V) k T := by
  intro hbd
  have hmass : massNorm (U := U) (V := V) (k - 1)
      (boundaryOperator (U := U) (V := V) k T) = 0 :=
    massNorm_boundary_eq_zero (U := U) (V := V) k T hbd
  simp [flatNorm, hmass]

end Boundary

end Topology
