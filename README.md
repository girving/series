Power series arithmetic in Lean
===============================

[![build](https://github.com/girving/series/actions/workflows/lean.yml/badge.svg)](https://github.com/girving/series/actions/workflows/lean.yml)

Exact and conservative power series arithmetic in Lean, built on top of the approximate arithmetic
machinery in [interval](https://github.com/girving/interval). The goal is reasonably fast, fully
formalised, one-dimensional, truncated power series arithmetic over a variety of arithmetic classes:
floating point interval arithmetic, naturals, rationals, dyadic rationals, etc.

We support the following power series operations, all of which are proven to approximate the
low-order derivatives of their equivalent operations on $C^n$-smooth functions:

1. **Ring operations**, using [Karatsuba multiplication](https://github.com/girving/series/blob/main/Series/Series/Mul.lean)
2. **Generic power series [Newton solves](https://github.com/girving/series/blob/main/Series/Series/Newton.lean)**, taking advantage of quadratic convergence for speed
3. **Series [inverse](https://github.com/girving/series/blob/main/Series/Series/Inverse.lean) and
   [square root](https://github.com/girving/series/blob/main/Series/Series/Sqrt.lean)** via Newton's
   method, specialised so that they work on monic series without requiring scalar division (for
   square root, we need division by 2, so dyadic rationals are useful).
4. **Miscellaneous:** Shifts / multiplication by $z ^ n$ and sums of series coefficients.

For an example on a nontrivial power series, [bottcher](https://github.com/girving/bottcher) uses
this repo to compute series coefficients of the Böttcher series of the Mandelbrot set at infinity.
The Böttcher series describes the analytic homeomorphism from the complement of the closed unit disk
to the complement of the Mandelbrot set, and can also be used to (weakly)
[upper bound the area of the set](https://github.com/girving/bottcher/blob/66851ffbca467cfbaf857531efdc737e968547d3/Bottcher/Actual.lean#L21). The `bottcher` repo is also an
example of a [custom Newton solver](https://github.com/girving/bottcher/blob/66851ffbca467cfbaf857531efdc737e968547d3/Bottcher/Pray.lean#L214), and indeed this custom Newton
solver uses both inverse and square root (each Newton solvers), of which square root builds on
inverse.

## Building

1. Install [`elan`](https://github.com/leanprover/elan) (`brew install elan-init` on Mac)
2. `lake build`
