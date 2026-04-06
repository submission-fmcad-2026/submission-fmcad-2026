/-
# Yang-Mills Mass Gap Formalization

This is the main entry point for the complete formalization of the 
Yang-Mills Mass Gap proof in Lean 4.

## Structure

### Algebraic Foundations (Manuscript Section 2.1-2.4)
- `YangMills.Algebra.SUN`: SU(N) group structure and Lie algebra
- `YangMills.Algebra.Representations`: Representation theory and characters
- `YangMills.Algebra.PeterWeyl`: Peter-Weyl expansion (Theorem 2.1)
- `YangMills.Algebra.LinkIntegral`: Link integrals (Lemma 2.2, Theorem 2.3)
- `YangMills.Algebra.WillmoreMajorization`: Geometric coercivity (Theorem 2.5)

### Geometric Measure Theory (Manuscript Section 2.5)
- `YangMills.Geometry.Grassmannian`: Grassmannian G(n,k) with Frobenius metric
- `YangMills.Geometry.Varifold`: General and integral varifolds
- `YangMills.Geometry.Rectifiability`: Countably k-rectifiable sets
- `YangMills.Geometry.FirstVariation`: First variation and mean curvature
- `YangMills.Geometry.Willmore`: Willmore energy and monotonicity

### Topology and Currents
- `YangMills.Topology.Currents`: General currents and flat norm
- `YangMills.Topology.RectifiableCurrents`: Rectifiable currents
- `YangMills.Topology.Vertex`: Vertex structures

### Physics
- `YangMills.Physics.BRST`: BRST cohomology (Section 7)
- `YangMills.Physics.StatisticalMechanics`: Cluster expansion (Section 8)
- `YangMills.Physics.MassGap`: Main mass gap theorem (Section 9)

## Main Theorem

`Physics.yang_mills_mass_gap`: For SU(N) Yang-Mills in 4D with g > 0, 
the spectral mass gap Δ_spec > 0.

## References
- LaTeX manuscript: Yang-Mils.tex by Yves-Landry Simo Yomgni
-/

import YangMills.Basic

-- Algebraic Foundations (Section 2.1-2.4)
import YangMills.Algebra.SUN
import YangMills.Algebra.MatrixFoundation
import YangMills.Algebra.Representations
import YangMills.Algebra.PeterWeyl
import YangMills.Algebra.LinkIntegral
import YangMills.Algebra.WillmoreMajorization

-- Geometric Measure Theory (Section 2.5)
import YangMills.Geometry.Grassmannian
import YangMills.Geometry.Varifold
import YangMills.Geometry.Rectifiability
import YangMills.Geometry.FirstVariation
import YangMills.Geometry.Willmore
import YangMills.Geometry.IntegralVarifold
import YangMills.Geometry.Integrability
import YangMills.Geometry.Monotonicity
import YangMills.Geometry.Orthogonality
import YangMills.Geometry.Renormalization
import YangMills.Geometry.MassGapConclusion

-- Topology and Currents
import YangMills.Topology.Currents
import YangMills.Topology.RectifiableCurrents
import YangMills.Topology.Vertex

-- Physics
import YangMills.Physics.BRST
import YangMills.Physics.StatisticalMechanics
import YangMills.Physics.MassGap
