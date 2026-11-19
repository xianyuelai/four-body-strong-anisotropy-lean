# Four-body balanced configurations under strong anisotropy

Lean 4 formalization of the accompanying manuscript.

- [Manuscript PDF](paper/four_body_strong_anisotropy_pro_v2.pdf)
- [Manuscript TeX source](paper/four_body_strong_anisotropy_pro_v2.tex)
- [Lean entry point](Paper.lean)
- [Theorem 1.1 in Lean](FourBody/MainTheorem.lean)

For any fixed four positive masses, all sufficiently large anisotropy parameters yield exactly 192 planar balanced configurations with multiplier one, fixed labels and axes, and no symmetry quotient. There are 24 solutions on each coordinate axis and 144 noncollinear solutions. Every solution is nondegenerate on the six-dimensional center-of-mass-zero space.

## Build

Install Lean through [elan](https://github.com/leanprover/elan). The repository pins Lean 4.33.1 and the exact dependency commits. A first build may fetch the dependencies.

```sh
lake build Paper
```

The release preserves the Lean source and dependency configuration from the manuscript v2 verification snapshot.
