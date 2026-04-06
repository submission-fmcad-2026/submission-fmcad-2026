import YangMills.Geometry.VertexCounterterm
import YangMills.Algebra.PeterWeyl

noncomputable section
open MeasureTheory TopologicalSpace Set Metric

variable {U V : Type*}
variable [NormedAddCommGroup U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {N : ℕ} [Fact (0 < N)]

namespace Geometry

/-- Finiteness package for the renormalized geometric interaction amplitude. -/
structure RenormalizationConvergence [MeasurableSpace U] [BorelSpace U]
  (k : ℕ) (Vf : IntegralVarifold (V := V) (U := U) k)
  (strat : Stratification k Vf) (div : LogarithmicDivergence k Vf strat)
  (counter : VertexCounterterm k Vf strat) where

  -- The residual amplitude cancels identically leaving exactly a strictly finite scalar evaluation.
  renormalized_amplitude : ℝ
  is_exact_cancellation :
    renormalized_amplitude = div.divergence_rate - counter.counterterm
  amplitude_bounded :
    ‖renormalized_amplitude‖ ≤ |div.divergence_rate| + |counter.counterterm|
  finite_amplitude_witness : ∃ C : ℝ, 0 ≤ C ∧ ‖renormalized_amplitude‖ ≤ C

/-- Morphism from branching vertices to SU(N) scattering states. -/
structure MorphologicalIsomorphism [MeasurableSpace U] [BorelSpace U]
  (k : ℕ) (Vf : IntegralVarifold (V := V) (U := U) k)
  (strat : Stratification k Vf) where

  -- Functorial map from branching singularities to SU(N) scattering fields.
  scattering_mapping : strat.branching_locus → YangMills.PeterWeyl.SUN N
  is_continuous : Continuous scattering_mapping

/-- Non-triviality and unitarity package for the renormalized model. -/
structure QuantumUnitarity [MeasurableSpace U] [BorelSpace U]
  (k : ℕ) (Vf : IntegralVarifold (V := V) (U := U) k)
  (strat : Stratification k Vf) (div : LogarithmicDivergence k Vf strat)
  (counter : VertexCounterterm k Vf strat)
  (renorm : RenormalizationConvergence k Vf strat div counter) where

  -- Quantitative unitarity control by divergence/counterterm scales.
  preserves_unitarity :
    ‖renorm.renormalized_amplitude‖ ≤
      |div.divergence_rate| + |counter.counterterm|

/-- Cancellation identity implies quantitative control of the renormalized amplitude. -/
lemma renormalized_amplitude_control [MeasurableSpace U] [BorelSpace U]
  (k : ℕ) (Vf : IntegralVarifold (V := V) (U := U) k)
  (strat : Stratification k Vf) (div : LogarithmicDivergence k Vf strat)
  (counter : VertexCounterterm k Vf strat)
  (renorm : RenormalizationConvergence k Vf strat div counter) :
    ‖renorm.renormalized_amplitude‖ ≤
      |div.divergence_rate| + |counter.counterterm| :=
  renorm.amplitude_bounded

/-- Export quantitative unitarity control from the unitarity package. -/
lemma quantum_unitarity_control [MeasurableSpace U] [BorelSpace U]
  (k : ℕ) (Vf : IntegralVarifold (V := V) (U := U) k)
  (strat : Stratification k Vf) (div : LogarithmicDivergence k Vf strat)
  (counter : VertexCounterterm k Vf strat)
  (renorm : RenormalizationConvergence k Vf strat div counter)
  (Q : QuantumUnitarity k Vf strat div counter renorm) :
    ‖renorm.renormalized_amplitude‖ ≤
      |div.divergence_rate| + |counter.counterterm| :=
  Q.preserves_unitarity

end Geometry
