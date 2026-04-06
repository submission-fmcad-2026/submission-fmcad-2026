import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import YangMills.Geometry.Rectifiability
import YangMills.Topology.Currents

noncomputable section

open MeasureTheory TopologicalSpace Set
open Geometry

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable {U : Type*} [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
variable (k : ℕ)

namespace Topology

variable [ExteriorDifferential U V]

/--
An integer-rectifiable current is a current whose action is represented by
integration over a countably `k`-rectifiable set with integer multiplicity and
an orientation field.
-/
structure IntegerRectifiableCurrent
    (U : Type*) [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [ExteriorDifferential U V] (k : ℕ)
    extends GeneralCurrent U V k where
  μ : Measure U
  M : Set U
  measurable_M : MeasurableSet M
  finite_mass_on_support : μ M < ⊤
  theta : U → ℤ
  theta_measurable : Measurable theta
  theta_integrable :
    Integrable (fun x => (theta x : ℝ)) (Measure.restrict μ M)
  xi : U → V
  xi_measurable : Measurable xi
  xi_sq_integrable : Integrable (fun x => ‖xi x‖ ^ (2 : ℕ)) (Measure.restrict μ M)
  action_eq_integral : ∀ ω : TestForm U V k,
    toLinearMap ω = MeasureTheory.integral (Measure.restrict μ M)
      (fun x => (theta x : ℝ) * (‖ω.1.form x‖ * ‖xi x‖))

/--
`isIntegralCurrent T` means the boundary of `T` is also integer-rectifiable.
-/
def isIntegralCurrent (T : IntegerRectifiableCurrent U V k) : Prop :=
  ∃ dT : IntegerRectifiableCurrent U V (k - 1),
    dT.toGeneralCurrent.action =
      (boundaryOperator (U := U) (V := V) k T.toGeneralCurrent).action

def zeroIntegerRectifiableCurrent (k : ℕ) : IntegerRectifiableCurrent U V k where
  toLinearMap := 0
  μ := 0
  M := ∅
  measurable_M := by simp
  finite_mass_on_support := by simp
  theta := fun _ => 0
  theta_measurable := by simp
  theta_integrable := by simp
  xi := fun _ => 0
  xi_measurable := by simp
  xi_sq_integrable := by simp
  action_eq_integral := by
    intro ω
    simp

lemma zeroIntegerRectifiableCurrent_action (k : ℕ) :
    (zeroIntegerRectifiableCurrent (k := k) : IntegerRectifiableCurrent U V k).action =
      fun _ => 0 :=
  rfl

lemma boundaryAction_eq_zero (T : IntegerRectifiableCurrent U V k) :
    (boundaryOperator (U := U) (V := V) k T.toGeneralCurrent).action 0 = 0 := by
  exact GeneralCurrent.action_zero
    (T := boundaryOperator (U := U) (V := V) k T.toGeneralCurrent)

theorem isIntegralCurrent_of_boundary_representation
    (T : IntegerRectifiableCurrent U V k)
    (hboundary : ∃ dT : IntegerRectifiableCurrent U V (k - 1),
      dT.toGeneralCurrent.action =
        (boundaryOperator (U := U) (V := V) k T.toGeneralCurrent).action) :
    isIntegralCurrent k T :=
  hboundary

theorem zero_isIntegralCurrent (k : ℕ) :
    isIntegralCurrent k
      (zeroIntegerRectifiableCurrent (k := k) : IntegerRectifiableCurrent U V k) := by
  refine ⟨(zeroIntegerRectifiableCurrent (k := k - 1) : IntegerRectifiableCurrent U V (k - 1)), ?_⟩
  funext ω
  cases k with
  | zero => simp [zeroIntegerRectifiableCurrent, boundaryOperator]
  | succ k =>
    simp [zeroIntegerRectifiableCurrent, boundaryOperator]
    rfl

end Topology
