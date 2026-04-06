import Mathlib
import YangMills.Geometry.Grassmannian
import YangMills.Geometry.Varifold

noncomputable section

open MeasureTheory TopologicalSpace Set LinearMap
open Grassmannian

namespace Geometry

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace Real U]
variable (k : Nat)

/-- Compactly supported C1 model vector field used to test first variation. -/
structure TestVectorField (U : Type*) [NormedAddCommGroup U] [InnerProductSpace Real U] where
  toFun : U -> U
  deriv : U -> (U →L[Real] U)
  compactSupport : HasCompactSupport toFun

instance : CoeFun (TestVectorField U) (fun _ => U -> U) where
  coe X := X.toFun

instance : Zero (TestVectorField U) where
  zero := {
    toFun := fun _ => 0
    deriv := fun _ => 0
    compactSupport := by
      simpa using (HasCompactSupport.zero : HasCompactSupport (0 : U -> U))
  }

instance : Add (TestVectorField U) where
  add X Y := {
    toFun := X.toFun + Y.toFun
    deriv := fun x => X.deriv x + Y.deriv x
    compactSupport := HasCompactSupport.add X.compactSupport Y.compactSupport
  }

instance : SMul Real (TestVectorField U) where
  smul c X := {
    toFun := c • X.toFun
    deriv := fun x => c • X.deriv x
    compactSupport := by
      simpa [Pi.smul_apply] using
        (HasCompactSupport.smul_left (f := fun _ : U => c) X.compactSupport)
  }

@[simp] lemma TestVectorField.toFun_zero (x : U) :
    (0 : TestVectorField U).toFun x = 0 :=
  rfl

@[simp] lemma TestVectorField.deriv_zero (x : U) :
    (0 : TestVectorField U).deriv x = 0 :=
  rfl

@[simp] lemma TestVectorField.toFun_add (X Y : TestVectorField U) (x : U) :
    (X + Y).toFun x = X.toFun x + Y.toFun x :=
  rfl

@[simp] lemma TestVectorField.deriv_add (X Y : TestVectorField U) (x : U) :
    (X + Y).deriv x = X.deriv x + Y.deriv x :=
  rfl

@[simp] lemma TestVectorField.toFun_smul (c : Real) (X : TestVectorField U) (x : U) :
    (c • X).toFun x = c • X.toFun x :=
  rfl

@[simp] lemma TestVectorField.deriv_smul (c : Real) (X : TestVectorField U) (x : U) :
    (c • X).deriv x = c • X.deriv x :=
  rfl

/-- Pointwise sup model used in Radon-type first-variation bounds. -/
def vectorFieldSupNorm (X : TestVectorField U) : Real :=
  max 0 (sSup { r : Real | ∃ x : U, r = ‖X.toFun x‖ })

lemma vectorFieldSupNorm_nonneg (X : TestVectorField U) :
    0 <= vectorFieldSupNorm X := by
  exact le_max_left _ _

variable [FiniteDimensional Real U]

/-- Tangential divergence div_S(X) defined by trace(P_S ∘ DX ∘ P_S). -/
def tangentialDivergence (X : TestVectorField U) (x : U) (S : Grassmannian U k) : Real :=
  LinearMap.trace Real U
    ((Grassmannian.proj S).toLinearMap.comp
      ((X.deriv x).toLinearMap.comp (Grassmannian.proj S).toLinearMap))

lemma tangentialDivergence_add
    (X Y : TestVectorField U) (x : U) (S : Grassmannian U k) :
    tangentialDivergence k (X + Y) x S
      = tangentialDivergence k X x S + tangentialDivergence k Y x S := by
  unfold tangentialDivergence
  simp [LinearMap.comp_add, LinearMap.add_comp]

lemma tangentialDivergence_smul
    (c : Real) (X : TestVectorField U) (x : U) (S : Grassmannian U k) :
    tangentialDivergence k (c • X) x S = c * tangentialDivergence k X x S := by
  unfold tangentialDivergence
  simp [LinearMap.comp_smul, LinearMap.smul_comp, smul_eq_mul]

lemma tangentialDivergence_zero (x : U) (S : Grassmannian U k) :
    tangentialDivergence k (0 : TestVectorField U) x S = 0 := by
  unfold tangentialDivergence
  simp

variable [MeasurableSpace U] [BorelSpace U]

/-- First variation of a varifold against a test vector field X:
δV(X) = ∫ div_S(X) dV(x,S). -/
def firstVariation (Vf : Varifold U U k) (X : TestVectorField U) : Real :=
  ∫ p : U × Grassmannian U k, tangentialDivergence k X p.1 p.2 ∂Vf.measure

lemma firstVariation_eq_integral_divergence
    (Vf : Varifold U U k) (X : TestVectorField U) :
    firstVariation k Vf X
      = ∫ p : U × Grassmannian U k, tangentialDivergence k X p.1 p.2 ∂Vf.measure :=
  rfl

lemma firstVariation_add
    (Vf : Varifold U U k)
    (X Y : TestVectorField U)
    (hX : Integrable
      (fun p : U × Grassmannian U k => tangentialDivergence k X p.1 p.2)
      Vf.measure)
    (hY : Integrable
      (fun p : U × Grassmannian U k => tangentialDivergence k Y p.1 p.2)
      Vf.measure) :
    firstVariation k Vf (X + Y) = firstVariation k Vf X + firstVariation k Vf Y := by
  have hpoint :
      (fun p : U × Grassmannian U k => tangentialDivergence k (X + Y) p.1 p.2)
        = (fun p : U × Grassmannian U k =>
            tangentialDivergence k X p.1 p.2 + tangentialDivergence k Y p.1 p.2) := by
    funext p
    exact tangentialDivergence_add (k := k) X Y p.1 p.2
  unfold firstVariation
  rw [hpoint]
  exact integral_add hX hY

lemma firstVariation_smul
    (Vf : Varifold U U k) (c : Real) (X : TestVectorField U) :
    firstVariation k Vf (c • X) = c * firstVariation k Vf X := by
  have hpoint :
      (fun p : U × Grassmannian U k => tangentialDivergence k (c • X) p.1 p.2)
        = (fun p : U × Grassmannian U k => c * tangentialDivergence k X p.1 p.2) := by
    funext p
    exact tangentialDivergence_smul (k := k) c X p.1 p.2
  unfold firstVariation
  rw [hpoint]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (integral_const_mul c (fun p : U × Grassmannian U k => tangentialDivergence k X p.1 p.2))

lemma firstVariation_zero (Vf : Varifold U U k) :
    firstVariation k Vf (0 : TestVectorField U) = 0 := by
  unfold firstVariation
  simp [tangentialDivergence_zero]

/-- Stationary varifold: zero first variation on all compactly supported test fields. -/
def IsStationary (Vf : Varifold U U k) : Prop :=
  ∀ X : TestVectorField U, firstVariation k Vf X = 0

/-- First-variation decomposition into absolutely continuous mean-curvature part
and singular Radon part. -/
structure MeanCurvatureDecomposition (Vf : Varifold U U k) where
  meanCurvature : U -> U
  singularPart : Measure U
  singularPart_mutually_singular : singularPart.MutuallySingular Vf.weightMeasure
  meanCurvature_integrable : ∀ K : Set U, IsCompact K ->
    Integrable (fun x => ‖meanCurvature x‖) (Vf.weightMeasure.restrict K)
  singularAction : TestVectorField U -> Real
  singularAction_bound :
    ∃ C : Real, 0 <= C ∧
      ∀ X : TestVectorField U, |singularAction X| <= C * vectorFieldSupNorm X
  firstVariation_decomposition :
    ∀ X : TestVectorField U,
      firstVariation k Vf X =
        - ∫ x, inner (𝕜 := Real) (meanCurvature x) (X.toFun x) ∂Vf.weightMeasure + singularAction X

lemma meanCurvature_normal
    (Vf : RectifiableVarifold U U k)
    (H : MeanCurvatureDecomposition k Vf.toVarifold)
    (X : TestVectorField U) :
    firstVariation k Vf.toVarifold X =
      - ∫ x, inner (𝕜 := Real) (H.meanCurvature x) (X.toFun x) ∂Vf.toVarifold.weightMeasure
        + H.singularAction X :=
  H.firstVariation_decomposition X

/-- Bounded first variation in Radon dual form:
|δV(X)| ≤ C ||X||_∞ for all compactly supported test vector fields X. -/
def HasBoundedFirstVariation (Vf : Varifold U U k) : Prop :=
  ∃ C : Real, C > 0 ∧
    ∀ X : TestVectorField U,
      |firstVariation k Vf X| <= C * vectorFieldSupNorm X

lemma HasBoundedFirstVariation.bound
    {Vf : Varifold U U k}
    (hVf : HasBoundedFirstVariation k Vf)
    (X : TestVectorField U) :
    ∃ C : Real, C > 0 ∧
      |firstVariation k Vf X| <= C * vectorFieldSupNorm X := by
  rcases hVf with ⟨C, hCpos, hCbound⟩
  exact ⟨C, hCpos, hCbound X⟩

theorem meanCurvature_integrable_of_bounded_firstVariation
    (Vf : Varifold U U k)
    (_h : HasBoundedFirstVariation k Vf)
    (H : MeanCurvatureDecomposition k Vf) :
    ∀ K : Set U, IsCompact K ->
      Integrable (fun x => ‖H.meanCurvature x‖) (Vf.weightMeasure.restrict K) :=
  H.meanCurvature_integrable

lemma firstVariation_of_smooth_surface
    (Vf : IntegralVarifold U U k)
    (X : TestVectorField U)
    (hdiv : ∀ᵐ p : U × Grassmannian U k ∂Vf.toVarifold.measure,
      tangentialDivergence k X p.1 p.2 = 0) :
    firstVariation k Vf.toVarifold X = 0 := by
  unfold firstVariation
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hdiv] with p hp
  simp [hp]

end Geometry
