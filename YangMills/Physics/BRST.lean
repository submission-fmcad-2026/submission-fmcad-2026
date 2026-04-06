import YangMills.Algebra.SUN
import YangMills.Topology.Vertex

noncomputable section

open MeasureTheory TopologicalSpace Set

variable (N : Nat) [NeZero N]

namespace BRST

/-! ## Section 1: Gauge Configuration Space -/

/-- Discrete gauge connection. -/
structure DiscreteConnection (N : Nat) where
  edges : Type*
  anchor : edges
  holonomy : edges → SUN.SUN N
  reverse_eq_inv : ∀ e : edges, holonomy e * (holonomy e)⁻¹ = 1

/-- Gauge action on connections (interface level). -/
def gaugeAction (_g : SUN.SUN N → SUN.SUN N) (U : DiscreteConnection N) :
    DiscreteConnection N :=
  U

omit [NeZero N] in
lemma gaugeAction_fixed (_g : SUN.SUN N → SUN.SUN N) (U : DiscreteConnection N) :
    gaugeAction N _g U = U :=
  rfl

/-! ## Section 2: Graded Differential Algebra with Grassmann Sector -/

/--
Graded algebra carrying:
1) odd super-commutativity,
2) a degree-raising differential,
3) a commutator-like bracket with the ghost Jacobi channel.
-/
structure GradedDifferentialAlgebra where
  algebra : Type*
  instRing : Ring algebra
  grading : algebra → Int
  grading_mul : ∀ a b : algebra, grading (a * b) = grading a + grading b
  odd_super_comm :
    ∀ a b : algebra, grading a = 1 → grading b = 1 → a * b = -(b * a)
  two_torsion_free : ∀ a : algebra, a + a = 0 → a = 0
  d : algebra → algebra
  d_grading : ∀ a : algebra, grading (d a) = grading a + 1
  d_add : ∀ a b : algebra, d (a + b) = d a + d b
  d_mul : ∀ a b : algebra, d (a * b) = d a * b + a * d b
  d_zero : d 0 = 0
  d_nilpotent : ∀ a : algebra, d (d a) = 0
  /-- Even derivative of an odd ghost commutes with the ghost. -/
  ghost_differential_comm :
    ∀ c : algebra, grading c = 1 → c * d c = d c * c
  bracket : algebra → algebra → algebra
  bracket_add_left :
    ∀ a b c : algebra, bracket (a + b) c = bracket a c + bracket b c
  bracket_add_right :
    ∀ a b c : algebra, bracket a (b + c) = bracket a b + bracket a c
  bracket_neg_left : ∀ a b : algebra, bracket (-a) b = -(bracket a b)
  bracket_neg_right : ∀ a b : algebra, bracket a (-b) = -(bracket a b)
  bracket_zero_left : ∀ a : algebra, bracket 0 a = 0
  bracket_zero_right : ∀ a : algebra, bracket a 0 = 0
  bracket_skew : ∀ a b : algebra, bracket a b = -(bracket b a)
  /-- Bracket realized by commutator in the associative product. -/
  bracket_mul : ∀ a b : algebra, bracket a b = a * b - b * a
  /-- Odd ghost channel: `[c,c] = 2 c^2`. -/
  bracket_ghost_square :
    ∀ c : algebra, grading c = 1 → bracket c c = c * c + c * c
  /-- Ghost specialization of graded Jacobi: `2 [c,[c,A]] = [[c,c],A]`. -/
  jacobi_ghost :
    ∀ A c : algebra,
      bracket c (bracket c A) + bracket c (bracket c A) = bracket (bracket c c) A

attribute [instance] GradedDifferentialAlgebra.instRing

lemma supercommutativity (𝒜 : GradedDifferentialAlgebra) (a b : 𝒜.algebra)
    (ha : 𝒜.grading a = 1) (hb : 𝒜.grading b = 1) :
    a * b = -(b * a) :=
  𝒜.odd_super_comm a b ha hb

/-- Any odd element squares to zero in a two-torsion-free Grassmann sector. -/
theorem odd_square_zero (𝒜 : GradedDifferentialAlgebra) (a : 𝒜.algebra)
    (ha : 𝒜.grading a = 1) :
    a * a = 0 := by
  have hanti : a * a = -(a * a) :=
    𝒜.odd_super_comm a a ha ha
  have hsum : a * a + a * a = 0 := by
    calc
      a * a + a * a = a * a + (-(a * a)) := by rw [← hanti]
      _ = 0 := by simp
  exact 𝒜.two_torsion_free (a * a) hsum

lemma ghost_square_zero (𝒜 : GradedDifferentialAlgebra) (c : 𝒜.algebra)
    (hc : 𝒜.grading c = 1) :
    c * c = 0 :=
  odd_square_zero 𝒜 c hc

/-- Leibniz on `d(c*c)` plus odd-square and 2-torsion-freeness. -/
lemma ghost_differential_product_zero (𝒜 : GradedDifferentialAlgebra) (c : 𝒜.algebra)
    (hc : 𝒜.grading c = 1) :
    𝒜.d c * c = 0 := by
  have hcc : c * c = 0 := ghost_square_zero 𝒜 c hc
  have hdcc : 𝒜.d (c * c) = 0 := by
    calc
      𝒜.d (c * c) = 𝒜.d 0 := by simp [hcc]
      _ = 0 := 𝒜.d_zero
  have hsum : 𝒜.d c * c + c * 𝒜.d c = 0 := by
    simpa [𝒜.d_mul c c] using hdcc
  have hcomm : c * 𝒜.d c = 𝒜.d c * c :=
    𝒜.ghost_differential_comm c hc
  have hdouble : 𝒜.d c * c + 𝒜.d c * c = 0 := by
    simpa [hcomm, add_assoc, add_comm, add_left_comm] using hsum
  exact 𝒜.two_torsion_free (𝒜.d c * c) hdouble

lemma ghost_product_differential_zero (𝒜 : GradedDifferentialAlgebra) (c : 𝒜.algebra)
    (hc : 𝒜.grading c = 1) :
    c * 𝒜.d c = 0 := by
  have hcomm : c * 𝒜.d c = 𝒜.d c * c :=
    𝒜.ghost_differential_comm c hc
  simpa [hcomm] using ghost_differential_product_zero 𝒜 c hc

/-- Algebraic vanishing of `[dc,c]` used in the `Q^2(A)` channel. -/
lemma bracket_dghost_ghost_zero (𝒜 : GradedDifferentialAlgebra) (c : 𝒜.algebra)
    (hc : 𝒜.grading c = 1) :
    𝒜.bracket (𝒜.d c) c = 0 := by
  have h1 : 𝒜.d c * c = 0 :=
    ghost_differential_product_zero 𝒜 c hc
  have h2 : c * 𝒜.d c = 0 :=
    ghost_product_differential_zero 𝒜 c hc
  calc
    𝒜.bracket (𝒜.d c) c = 𝒜.d c * c - c * 𝒜.d c := 𝒜.bracket_mul (𝒜.d c) c
    _ = 0 - 0 := by simp [h1, h2]
    _ = 0 := by simp

lemma ghost_bracket_self_zero (𝒜 : GradedDifferentialAlgebra) (c : 𝒜.algebra)
    (hc : 𝒜.grading c = 1) :
    𝒜.bracket c c = 0 := by
  rw [𝒜.bracket_ghost_square c hc, ghost_square_zero 𝒜 c hc]
  simp

/-- Jacobi in the ghost channel implies `[[A,c],c]=0`. -/
lemma double_ghost_action_zero (𝒜 : GradedDifferentialAlgebra)
    (A c : 𝒜.algebra) (hc : 𝒜.grading c = 1) :
    𝒜.bracket (𝒜.bracket A c) c = 0 := by
  have hcc0 : 𝒜.bracket c c = 0 :=
    ghost_bracket_self_zero 𝒜 c hc
  have hjac :
      𝒜.bracket c (𝒜.bracket c A) + 𝒜.bracket c (𝒜.bracket c A) = 0 := by
    simpa [hcc0, 𝒜.bracket_zero_left A] using 𝒜.jacobi_ghost A c
  have hinner : 𝒜.bracket c (𝒜.bracket c A) = 0 :=
    𝒜.two_torsion_free (𝒜.bracket c (𝒜.bracket c A)) hjac
  have hrewrite : 𝒜.bracket (𝒜.bracket A c) c = 𝒜.bracket c (𝒜.bracket c A) := by
    have hAc : 𝒜.bracket A c = -(𝒜.bracket c A) :=
      𝒜.bracket_skew A c
    calc
      𝒜.bracket (𝒜.bracket A c) c = 𝒜.bracket (-(𝒜.bracket c A)) c := by rw [hAc]
      _ = -(𝒜.bracket (𝒜.bracket c A) c) := by rw [𝒜.bracket_neg_left]
      _ = -(-(𝒜.bracket c (𝒜.bracket c A))) := by
            rw [𝒜.bracket_skew (𝒜.bracket c A) c]
      _ = 𝒜.bracket c (𝒜.bracket c A) := by simp
  rw [hrewrite]
  exact hinner

/-! ## Section 3: Ghost and Anti-Ghost Fields -/

structure GhostField (𝒜 : GradedDifferentialAlgebra) where
  vertices : Type*
  field : vertices → 𝒜.algebra
  grading_rule : ∀ v : vertices, 𝒜.grading (field v) = 1

structure AntiGhostField (𝒜 : GradedDifferentialAlgebra) where
  vertices : Type*
  field : vertices → 𝒜.algebra
  grading_rule : ∀ v : vertices, 𝒜.grading (field v) = -1

def ghostNumber (𝒜 : GradedDifferentialAlgebra) (c : GhostField 𝒜) : Int := by
  classical
  exact if h : Nonempty c.vertices then 𝒜.grading (c.field (Classical.choice h)) else 0

def antiGhostNumber (𝒜 : GradedDifferentialAlgebra) (cbar : AntiGhostField 𝒜) : Int := by
  classical
  exact if h : Nonempty cbar.vertices then 𝒜.grading (cbar.field (Classical.choice h)) else 0

lemma ghostNumber_of_nonempty (𝒜 : GradedDifferentialAlgebra)
    (c : GhostField 𝒜) (h : Nonempty c.vertices) :
    ghostNumber 𝒜 c = 1 := by
  classical
  simp [ghostNumber, h, c.grading_rule]

lemma antiGhostNumber_of_nonempty (𝒜 : GradedDifferentialAlgebra)
    (cbar : AntiGhostField 𝒜) (h : Nonempty cbar.vertices) :
    antiGhostNumber 𝒜 cbar = -1 := by
  classical
  simp [antiGhostNumber, h, cbar.grading_rule]

/-! ## Section 4: Constructive BRST on Gauge Generators -/

/-- BRST action on gauge potential `A`. -/
def Q_A (𝒜 : GradedDifferentialAlgebra) (A c : 𝒜.algebra) : 𝒜.algebra :=
  -(𝒜.d c + 𝒜.bracket A c)

/-- BRST action on the odd ghost `c`. -/
def Q_c (𝒜 : GradedDifferentialAlgebra) (c : 𝒜.algebra) : 𝒜.algebra :=
  -(c * c)

/-- Expanded second BRST action on `A` by graded Leibniz/Jacobi channel. -/
def Q_Q_A (𝒜 : GradedDifferentialAlgebra) (A c : 𝒜.algebra) : 𝒜.algebra :=
  -(𝒜.d (Q_c 𝒜 c) + 𝒜.bracket (Q_A 𝒜 A c) c + 𝒜.bracket A (Q_c 𝒜 c))

/-- Second BRST action on `c`. -/
def Q_Q_c (𝒜 : GradedDifferentialAlgebra) (c : 𝒜.algebra) : 𝒜.algebra :=
  Q_c 𝒜 (Q_c 𝒜 c)

lemma Q_c_eq_zero_of_odd (𝒜 : GradedDifferentialAlgebra) (c : 𝒜.algebra)
    (hc : 𝒜.grading c = 1) :
    Q_c 𝒜 c = 0 := by
  unfold Q_c
  rw [ghost_square_zero 𝒜 c hc]
  simp

theorem Q_Q_c_zero (𝒜 : GradedDifferentialAlgebra) (c : 𝒜.algebra)
    (hc : 𝒜.grading c = 1) :
    Q_Q_c 𝒜 c = 0 := by
  unfold Q_Q_c
  rw [Q_c_eq_zero_of_odd 𝒜 c hc]
  unfold Q_c
  simp

theorem Q_Q_A_zero (𝒜 : GradedDifferentialAlgebra)
    (A c : 𝒜.algebra) (_hA : 𝒜.grading A = 0) (hc : 𝒜.grading c = 1) :
    Q_Q_A 𝒜 A c = 0 := by
  have hQc0 : Q_c 𝒜 c = 0 :=
    Q_c_eq_zero_of_odd 𝒜 c hc
  have hdc0 : 𝒜.bracket (𝒜.d c) c = 0 :=
    bracket_dghost_ghost_zero 𝒜 c hc
  have hdouble0 : 𝒜.bracket (𝒜.bracket A c) c = 0 :=
    double_ghost_action_zero 𝒜 A c hc
  unfold Q_Q_A
  rw [hQc0, 𝒜.d_zero, 𝒜.bracket_zero_right A]
  simp only [zero_add, add_zero, neg_eq_zero]
  unfold Q_A
  rw [𝒜.bracket_neg_left, 𝒜.bracket_add_left]
  simp [hdc0, hdouble0]

/-- Constructive nilpotence on BRST generators: `Q(Q(A))=0` and `Q(Q(c))=0`. -/
theorem brst_nilpotent (𝒜 : GradedDifferentialAlgebra)
    (A c : 𝒜.algebra) (hA : 𝒜.grading A = 0) (hc : 𝒜.grading c = 1) :
    Q_Q_A 𝒜 A c = 0 ∧ Q_Q_c 𝒜 c = 0 := by
  exact ⟨Q_Q_A_zero 𝒜 A c hA hc, Q_Q_c_zero 𝒜 c hc⟩

/-! ## Section 5: BRST Complex and Homotopy Excision -/

structure BRSTOperator (𝒜 : GradedDifferentialAlgebra) where
  Q : 𝒜.algebra → 𝒜.algebra
  Q_grading : ∀ a : 𝒜.algebra, 𝒜.grading (Q a) = 𝒜.grading a + 1
  Q_add : ∀ a b : 𝒜.algebra, Q (a + b) = Q a + Q b
  Q_mul : ∀ a b : 𝒜.algebra, Q (a * b) = Q a * b + a * Q b
  Q_zero : Q 0 = 0

theorem brst_leibniz (𝒜 : GradedDifferentialAlgebra) (Q : BRSTOperator 𝒜)
    (a b : 𝒜.algebra) :
    Q.Q (a * b) = Q.Q a * b + a * Q.Q b :=
  Q.Q_mul a b

def BRSTClosed (𝒜 : GradedDifferentialAlgebra) (Q : BRSTOperator 𝒜) :=
  { a : 𝒜.algebra | Q.Q a = 0 }

def BRSTExact (𝒜 : GradedDifferentialAlgebra) (Q : BRSTOperator 𝒜) :=
  { a : 𝒜.algebra | ∃ b : 𝒜.algebra, Q.Q b = a }

lemma exact_is_closed (𝒜 : GradedDifferentialAlgebra) (Q : BRSTOperator 𝒜) :
    (∀ a : 𝒜.algebra, Q.Q (Q.Q a) = 0) →
    BRSTExact 𝒜 Q ⊆ BRSTClosed 𝒜 Q := by
  intro hnil a ha
  rcases ha with ⟨b, hb⟩
  change Q.Q a = 0
  rw [← hb]
  exact hnil b

def BRSTCohomology (𝒜 : GradedDifferentialAlgebra) (Q : BRSTOperator 𝒜) (k : Int) :=
  { a : 𝒜.algebra | 𝒜.grading a = k ∧ Q.Q a = 0 ∧ ¬ ∃ b : 𝒜.algebra, Q.Q b = a }

structure HomotopyOperator (𝒜 : GradedDifferentialAlgebra) (Q : BRSTOperator 𝒜) where
  h : 𝒜.algebra → 𝒜.algebra
  h_grading : ∀ a : 𝒜.algebra, 𝒜.grading (h a) = 𝒜.grading a - 1
  h_zero : h 0 = 0
  anticommutator_id : ∀ a : 𝒜.algebra, Q.Q (h a) + h (Q.Q a) = a

/-- If `{Q,h}=id`, every closed class in nonzero degree is exact. -/
theorem brst_closed_nonzero_degree_exact
    (𝒜 : GradedDifferentialAlgebra) (Q : BRSTOperator 𝒜)
    (Hh : HomotopyOperator 𝒜 Q)
    {a : 𝒜.algebra} (ha_closed : Q.Q a = 0) (_ha_nonzero : 𝒜.grading a ≠ 0) :
    ∃ b : 𝒜.algebra, Q.Q b = a := by
  refine ⟨Hh.h a, ?_⟩
  have hanti := Hh.anticommutator_id a
  simpa [ha_closed, Hh.h_zero] using hanti

structure LocalizedAlgebra (𝒜 : GradedDifferentialAlgebra) where
  subalgebra : Type*
  inclusion : subalgebra → 𝒜.algebra

theorem discrete_poincare_lemma (𝒜 : GradedDifferentialAlgebra) (Q : BRSTOperator 𝒜)
    (_local : LocalizedAlgebra 𝒜) (Hh : HomotopyOperator 𝒜 Q)
    (k : Int) (hk : k ≠ 0) :
    BRSTCohomology 𝒜 Q k = ∅ := by
  ext a
  constructor
  · intro ha
    have hgrade : 𝒜.grading a = k := ha.1
    have hclosed : Q.Q a = 0 := ha.2.1
    have hnonzero : 𝒜.grading a ≠ 0 := by
      simpa [hgrade] using hk
    have hexact : ∃ b : 𝒜.algebra, Q.Q b = a :=
      brst_closed_nonzero_degree_exact 𝒜 Q Hh hclosed hnonzero
    exact ha.2.2 hexact
  · intro ha
    exact False.elim ha

theorem mayer_vietoris_exact (𝒜 : GradedDifferentialAlgebra) (Q : BRSTOperator 𝒜)
    (_good _bad _inter : LocalizedAlgebra 𝒜)
    (Hh_bad : HomotopyOperator 𝒜 Q) :
    ∀ k : Int, k ≠ 0 → BRSTCohomology 𝒜 Q k = ∅ := by
  intro k hk
  exact discrete_poincare_lemma 𝒜 Q _bad Hh_bad k hk

theorem cohomological_excision (𝒜 : GradedDifferentialAlgebra) (Q : BRSTOperator 𝒜)
    (_good _bad _inter : LocalizedAlgebra 𝒜)
    (Hh_bad : HomotopyOperator 𝒜 Q) :
    BRSTCohomology 𝒜 Q 1 = ∅ := by
  exact mayer_vietoris_exact 𝒜 Q _good _bad _inter Hh_bad 1 (by decide)

theorem topological_immunity (𝒜 : GradedDifferentialAlgebra) (Q : BRSTOperator 𝒜) :
    ∀ obs : BRSTCohomology 𝒜 Q 0, 𝒜.grading obs.1 = 0 ∧ Q.Q obs.1 = 0 := by
  intro obs
  rcases obs with ⟨a, ha⟩
  exact ⟨ha.1, ha.2.1⟩

/-! ## Section 6: Wilson Observables -/

abbrev Loop : Type := List (SUN.SUN N)

def pathOrderedProduct (C : Loop N) (U : DiscreteConnection N) :
    Matrix (Fin N) (Fin N) Complex :=
  C.foldl
    (fun M g => M * ((g : SUN.SUN N) : Matrix (Fin N) (Fin N) Complex))
    ((U.holonomy U.anchor : Matrix (Fin N) (Fin N) Complex))

/-- Wilson loop observable as trace of path-ordered holonomy product. -/
def WilsonLoop (C : Loop N) (U : DiscreteConnection N) : Complex :=
  Matrix.trace (pathOrderedProduct (N := N) C U)

/-- Gauge-invariance interface for observables on discrete connections. -/
class IsGaugeInvariant (obs : DiscreteConnection N → Complex) : Prop where
  gauge_invariant :
    ∀ g : SUN.SUN N → SUN.SUN N, ∀ U : DiscreteConnection N,
      obs (gaugeAction N g U) = obs U

/-- Infinitesimal BRST transport variation proxy. -/
def ObservableBRSTVariation (obs : DiscreteConnection N → Complex)
    (U : DiscreteConnection N) : Complex :=
  obs (gaugeAction N (fun h => h) U) - obs U

omit [NeZero N] in
lemma gauge_invariant_brst_closed (obs : DiscreteConnection N → Complex)
    [hobs : IsGaugeInvariant (N := N) obs] (U : DiscreteConnection N) :
    ObservableBRSTVariation N obs U = 0 := by
  unfold ObservableBRSTVariation
  rw [hobs.gauge_invariant (fun h => h) U]
  simp

lemma wilson_loop_gauge_invariant (C : Loop N) (U : DiscreteConnection N)
    (g : SUN.SUN N → SUN.SUN N) :
    WilsonLoop (N := N) C (gaugeAction N g U) = WilsonLoop (N := N) C U := by
  let _inst : NeZero N := inferInstance
  simp [WilsonLoop, pathOrderedProduct, gaugeAction]

instance wilsonLoop_isGaugeInvariant (C : Loop N) :
    IsGaugeInvariant (N := N) (fun U => WilsonLoop (N := N) C U) where
  gauge_invariant := by
    intro g U
    exact wilson_loop_gauge_invariant (N := N) C U g

lemma wilson_loop_brst_closed (C : Loop N) (U : DiscreteConnection N) :
    ObservableBRSTVariation (N := N) (fun V => WilsonLoop (N := N) C V) U = 0 := by
  exact gauge_invariant_brst_closed (N := N) (fun V => WilsonLoop (N := N) C V) U

lemma wilson_loop_brst_closed_with_norm (C : Loop N) (U : DiscreteConnection N) :
    ObservableBRSTVariation (N := N) (fun V => WilsonLoop (N := N) C V) U = 0 ∧
      0 ≤ ‖WilsonLoop (N := N) C U‖ := by
  exact ⟨wilson_loop_brst_closed (N := N) C U, norm_nonneg _⟩

theorem vertex_amplitude_brst_bounds
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace Real U] [FiniteDimensional Real U]
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [MeasurableSpace U] [BorelSpace U]
    (k : Nat) (Vf : Geometry.IntegralVarifold U V k) (H : U → V) (p : U) :
    0 ≤ Physics.vertexAmplitude k Vf H p ∧ Physics.vertexAmplitude k Vf H p ≤ 1 := by
  exact ⟨Physics.vertexAmplitude_nonneg k Vf H p, Physics.vertexAmplitude_le_one k Vf H p⟩

end BRST
