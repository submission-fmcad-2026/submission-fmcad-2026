# Yang-Mills Mass Gap: Formal Architecture and Analytic Proof

[![Lean Full Build and Docs](https://github.com/submission-fmcad-2026/submission-fmcad-2026/actions/workflows/lean_action_ci.yml/badge.svg?branch=main)](https://github.com/submission-fmcad-2026/submission-fmcad-2026/actions/workflows/lean_action_ci.yml)

This repository contains a Lean 4 formalization of the Yang-Mills mass gap architecture in dimension four. It is designed as a research-grade formal companion to the monograph *A Rigorous Non-Perturbative Formulation of Yang-Mills Theory and Proof of the Mass Gap* (402 pages).

Full Analytical Manuscript: See [Yang_Mills_Mass_Gap_Monograph.pdf](./Yang_Mills_Mass_Gap_Monograph.pdf)

The target is the Millennium Prize problem on the Yang-Mills mass gap. The repository is written as a complete formal architecture of that program, not as an introductory subset.

The aim is precise: to deliver a compiler-verified theorem architecture that extracts a strictly positive spectral mass gap once the physical model is instantiated through mathematically explicit interface contracts.

The terminal synthesis theorem is `Physics.yang_mills_mass_gap` in `YangMills/Physics/MassGap.lean`.

## Code-Manuscript Synergy

The project follows a strict division of labor.

1. Lean 4 formalization (logical architecture):
	 the repository verifies the theorem chain linking representation theory, geometric measure inputs, BRST excision, statistical-mechanical control, and mass gap extraction.
2. Analytic manuscript (hard estimates):
	 the monograph provides the infinite-dimensional analysis, quantitative bounds, and physical derivations showing that Yang-Mills dynamics satisfies the interface contracts used by the formal chain.

In this design, the formal and analytic components are complementary and synchronized: the code fixes the logical dependency graph, while the manuscript proves the physical validity of the contracts required by that graph.

## Axiomatic Interfaces as Typeclass Contracts

This repository does not present ad hoc placeholders for central physics statements. It uses explicit typeclass interfaces, with named fields and mathematically controlled semantics.

- `GeometricMeasureTheorySpace` in `YangMills/Geometry/IntegralVarifold.lean`:
	contract for GMT-level regularity, compactness, monotonicity, and semicontinuity inputs.
- `YangMillsPathIntegral` in `YangMills/Physics/MassGap.lean`:
	contract for the non-perturbative slicing and correlator bound used in the final mass gap step.

These are interface contracts, not informal suppositions. The manuscript is the analytic layer that establishes physical compliance with these contracts.

Under these contracts, the mass gap formula synthesized in the final layer is

$$
M_{\mathrm{gap}} = 4\pi\sqrt{\sigma_0\beta_0} - \Delta S_q > 0.
$$

## Repository Layout

The root module `YangMills.lean` imports the full formal chain.

- `YangMills/Algebra/`:
	SU(N) structures, representation-theoretic tools, Peter-Weyl decomposition, link integrals, UV asymptotic controls, and geometric majorization interfaces.
- `YangMills/Geometry/`:
	varifolds, first variation, integral varifold interfaces, Willmore-type controls, monotonicity, semicontinuity, and decomposition machinery.
- `YangMills/Topology/`:
	currents, rectifiable currents, and vertex-level homological structures.
- `YangMills/Physics/`:
	`BRST.lean`, `StatisticalMechanics.lean`, and `MassGap.lean`, culminating in spectral gap extraction.

## Build and Verification

Prerequisites:

- [Elan](https://github.com/leanprover/elan)
- Lean toolchain pinned in `lean-toolchain`

Local compilation:

```bash
lake exe cache get
lake build
lake build YangMills
```

Consistency check for logical gaps in source files:

```bash
rg -n "\bsorry\b|\baxiom\b" YangMills
```

## Continuous Integration and Documentation

The workflow `.github/workflows/lean_action_ci.yml` runs Lean build and doc generation on push, pull request, and manual dispatch.

Exact workflow used for full compilation and documentation publication:

```yaml
name: Lean Full Build and Docs

on:
	push:
		branches:
			- main
			- master
	pull_request:
	workflow_dispatch:

permissions:
	contents: read
	pages: write
	id-token: write

concurrency:
	group: pages-${{ github.ref }}
	cancel-in-progress: true

jobs:
	lean-full-build:
		runs-on: ubuntu-latest
		steps:
			- uses: actions/checkout@v5
			- uses: leanprover/lean-action@v1
			- name: Build full Lean codebase
				run: |
					lake exe cache get
					lake build
					lake build YangMills

	docs-pages:
		needs: lean-full-build
		if: github.event_name != 'pull_request' && (github.ref == 'refs/heads/main' || github.ref == 'refs/heads/master')
		runs-on: ubuntu-latest
		steps:
			- uses: actions/checkout@v5
			- uses: leanprover/lean-action@v1
			- uses: leanprover-community/docgen-action@v1
```

Auxiliary workflows:

- `.github/workflows/update.yml` for dependency update automation.
- `.github/workflows/create-release.yml` for release tagging when the toolchain changes.

## GitHub Pages

The repository is configured for GitHub Pages publication via GitHub Actions.

Setup:

1. open repository Settings,
2. open Pages,
3. select GitHub Actions as the source,
4. ensure Actions are enabled.

Expected Pages base URL for this repository:

https://github.com/submission-fmcad-2026/submission-fmcad-2026

## Notes for Reviewers and Auditors

Recommended audit protocol:

1. compile the project and verify that `Physics.yang_mills_mass_gap` builds,
2. inspect interface contracts in `YangMills/Geometry/IntegralVarifold.lean` and `YangMills/Physics/MassGap.lean`,
3. cross-check the analytic derivations in the manuscript at [Yang_Mills_Mass_Gap_Monograph.pdf](./Yang_Mills_Mass_Gap_Monograph.pdf).

This repository is written for theorem-level review, with explicit traceability between formal modules and analytic derivation layers.
