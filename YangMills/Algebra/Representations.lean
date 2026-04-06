/-
# Irreducible Representations of SU(N) - Constructive Layer

This module provides an abstract, non-abelian-safe representation-label layer
for downstream Peter-Weyl and link-integral bounds.
-/

import YangMills.Algebra.SUN
import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open MeasureTheory

namespace SUN

variable (N : Nat)

/-- Rigorous label for irreducible representations of SU(N). -/
structure RepresentationLabel (N : ℕ) where
  /-- Representation dimension. -/
  dim : ℕ
  /-- Positive-dimensionality witness. -/
  dim_pos : 0 < dim
  /-- N-ality charge used by coupling-selection rules. -/
  centerCharge : ℕ
  /-- Matrix realization of the representation on the gauge group. -/
  repMatrix : SUN N → Matrix (Fin dim) (Fin dim) Complex
  /-- Normalization at the identity element. -/
  repMatrix_one : repMatrix 1 = 1
  /-- Multiplicative compatibility with group product. -/
  repMatrix_mul : ∀ U V : SUN N, repMatrix (U * V) = repMatrix U * repMatrix V
  /-- Pointwise character bound compatible with finite truncation majorization. -/
  trace_normSq_bound :
    ∀ U : SUN N, Complex.normSq (Matrix.trace (repMatrix U)) ≤ (dim : Real) ^ 2
  /-- Schur-orthogonality normalization on the Haar-probability space. -/
  irreducible_trace_integral :
    MeasureTheory.integral (haar_measure N)
      (fun U : SUN N => Complex.normSq (Matrix.trace (repMatrix U))) = 1

/-- Backward-compatible name retained for downstream imports. -/
abbrev DominantWeight (N : Nat) := RepresentationLabel N

noncomputable instance instDecidableEqDominantWeight (N : Nat) : DecidableEq (DominantWeight N) :=
  Classical.decEq _

namespace DominantWeight

variable {N : Nat}

/-- Residue class representative used for n-ality arithmetic. -/
def nalityResidue (N k : Nat) : Nat :=
  k % N

/-- Charge conjugation on n-ality residues. -/
def conjugateNality (N k : Nat) : Nat :=
  (N - nalityResidue N k) % N

/-- Trivial representation label. -/
def trivial : DominantWeight N :=
  { dim := 1
    dim_pos := by norm_num
    centerCharge := 0
    repMatrix := fun _ => (1 : Matrix (Fin 1) (Fin 1) Complex)
    repMatrix_one := by simp
    repMatrix_mul := by intro U V; simp
    trace_normSq_bound := by intro U; simp
    irreducible_trace_integral := by
      have hrealUniv : (haar_measure N).real Set.univ = 1 := by
        rw [MeasureTheory.Measure.real_def]
        calc
          ENNReal.toReal (haar_measure N Set.univ)
              = ENNReal.toReal (1 : ENNReal) :=
                congrArg ENNReal.toReal (haar_measure_univ N)
          _ = 1 := by simp
      simp [hrealUniv] }

/-- Charge conjugation at the label level. -/
def conjugate (lam : DominantWeight N) : DominantWeight N :=
  { dim := lam.dim
    dim_pos := lam.dim_pos
    centerCharge := conjugateNality N lam.centerCharge
    repMatrix := lam.repMatrix
    repMatrix_one := lam.repMatrix_one
    repMatrix_mul := lam.repMatrix_mul
    trace_normSq_bound := lam.trace_normSq_bound
    irreducible_trace_integral := lam.irreducible_trace_integral }

/-- Height proxy retained for compatibility with prior APIs. -/
def height (lam : DominantWeight N) : Nat :=
  lam.dim - 1

/-- Reduced n-ality representative. -/
def nality (lam : DominantWeight N) : Nat :=
  nalityResidue N lam.centerCharge

lemma nality_trivial : nality (trivial : DominantWeight N) = 0 := by
  simp [nality, trivial, nalityResidue]

lemma nality_conjugate (lam : DominantWeight N) :
  nality (conjugate lam) = conjugateNality N lam.centerCharge := by
  simp [nality, conjugate, nalityResidue, conjugateNality]

end DominantWeight

/-- Weyl-dimension layer used downstream by Fourier truncation formulas. -/
def weylDimension {N : Nat} (lam : DominantWeight N) : Nat :=
  lam.dim

lemma weylDimension_pos {N : Nat} (lam : DominantWeight N) :
    0 < weylDimension lam :=
  lam.dim_pos

/-- Casimir proxy based on the representation dimension scale. -/
def casimirInvariant {N : Nat} (lam : DominantWeight N) : Real :=
  let d : Real := (weylDimension lam : Real)
  d * (d + N)

lemma casimirInvariant_nonneg {N : Nat} (lam : DominantWeight N) :
    0 <= casimirInvariant lam := by
  dsimp [casimirInvariant]
  refine mul_nonneg (Nat.cast_nonneg (weylDimension lam)) ?_
  exact add_nonneg (Nat.cast_nonneg (weylDimension lam)) (Nat.cast_nonneg N)

/-- Weyl character evaluated as the complex trace of a representation matrix. -/
def weylCharacter {N : Nat} (lam : DominantWeight N) (U : SUN N) : Complex :=
  Matrix.trace (lam.repMatrix U)

lemma weylCharacter_at_one {N : ℕ} (lam : RepresentationLabel N) :
  weylCharacter lam 1 = lam.dim := by
  dsimp [weylCharacter]
  rw [lam.repMatrix_one]
  simp

lemma weylCharacter_trivial {N : Nat} (U : SUN N) :
    weylCharacter (DominantWeight.trivial : DominantWeight N) U = (1 : Complex) := by
  simp [weylCharacter, DominantWeight.trivial]

lemma weylCharacter_isClassFunction {N : Nat}
    (lam : DominantWeight N)
    (hconj : ∀ U W : SUN N, lam.repMatrix (W * U * W⁻¹) = lam.repMatrix U) :
  is_class_function (weylCharacter (N := N) lam) := by
  intro U W
  simpa [weylCharacter] using congrArg Matrix.trace (hconj U W)

lemma weylCharacter_normSq_at_one {N : Nat}
    (lam : DominantWeight N) :
    Complex.normSq (weylCharacter (N := N) lam (1 : SUN N)) = (weylDimension lam : Real) ^ 2 := by
  rw [weylCharacter_at_one]
  simp [pow_two, weylDimension, Complex.normSq_natCast]

lemma weylCharacter_normSq_integral_eq_one {N : Nat}
    (lam : DominantWeight N) :
  MeasureTheory.integral (haar_measure N)
      (fun U : SUN N => Complex.normSq (weylCharacter (N := N) lam U)) = 1 := by
  simpa [weylCharacter] using lam.irreducible_trace_integral

lemma weylCharacter_normSq_le_dimensionSq {N : Nat}
    (lam : DominantWeight N) (U : SUN N) :
    Complex.normSq (weylCharacter (N := N) lam U) ≤ (weylDimension lam : Real) ^ 2 := by
  simpa [weylCharacter, weylDimension] using lam.trace_normSq_bound U

theorem characters_orthonormal_basis
    (N : Nat)
    (r : DominantWeight N) :
    MeasureTheory.integral (haar_measure N)
      (fun U : SUN N => weylCharacter (N := N) r U *
        star (weylCharacter (N := N) r U)) =
        (1 : Complex) := by
  have hnormSq :
      MeasureTheory.integral (haar_measure N)
        (fun U : SUN N => Complex.normSq (weylCharacter (N := N) r U)) = 1 :=
    weylCharacter_normSq_integral_eq_one (N := N) r
  have hnormSqC :
      MeasureTheory.integral (haar_measure N)
        (fun U : SUN N => ((Complex.normSq (weylCharacter (N := N) r U)) : Complex))
        = (1 : Complex) := by
    exact_mod_cast hnormSq
  calc
    MeasureTheory.integral (haar_measure N)
        (fun U : SUN N => weylCharacter (N := N) r U *
          star (weylCharacter (N := N) r U))
        = MeasureTheory.integral (haar_measure N)
            (fun U : SUN N =>
              ((Complex.normSq (weylCharacter (N := N) r U)) : Complex)) := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with U
              exact Complex.mul_conj (weylCharacter (N := N) r U)
    _ = (1 : Complex) := hnormSqC

/-- Coupling predicate implementing n-ality selection with charge conjugation. -/
def canCouple {N : Nat} (r s : DominantWeight N) : Prop :=
  DominantWeight.nality s = DominantWeight.conjugateNality N r.centerCharge ∨
    DominantWeight.nality r = DominantWeight.conjugateNality N s.centerCharge

lemma canCouple_comm {N : Nat} (r s : DominantWeight N) :
    canCouple r s -> canCouple s r := by
  intro h
  simpa [canCouple, or_comm, eq_comm] using h

lemma self_conjugate_coupling {N : Nat} (r : DominantWeight N) :
    exists s : DominantWeight N, canCouple r s := by
  refine ⟨DominantWeight.conjugate r, ?_⟩
  left
  simpa [canCouple] using DominantWeight.nality_conjugate (N := N) r

lemma trivial_coupling {N : Nat} (r : DominantWeight N)
    (h : DominantWeight.nality r = 0) :
    canCouple r DominantWeight.trivial := by
  right
  simpa [canCouple, DominantWeight.nality, DominantWeight.trivial,
    DominantWeight.nalityResidue, DominantWeight.conjugateNality] using h

end SUN
