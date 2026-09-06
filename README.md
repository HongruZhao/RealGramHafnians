# Shifted Anticoncentration for Real Gram Hafnians and Symmetric Gaussian Hafnians

Lean 4 proofs of **Theorem 2.1 and Theorem 2.3** of the paper by Hongru Zhao.
This repository contains the two headline results and the mathematical sources
needed to prove them. Both concern the hafnians of the actual Gaussian matrix
models defined in the sources.

**There are no additional mathematical axioms or admitted proofs in this
release.** The verification command below checks that the two public theorems
depend only on Lean's standard logical foundations: `propext`,
`Classical.choice`, and `Quot.sound`.

## Main results

The hafnian order is $n$, so the symmetric matrices have size $2n$ by $2n$.
Write

$$
\gamma_d=\frac{\Gamma((d-1)/2)}{\sqrt{2}\,\Gamma(d/2)},\qquad d>1.
$$

### Theorem 2.1: real Gram hafnians

Let $n\ge1$ and $k\ge n+1$. Let $X$ be a $k$ by $2n$ matrix of independent
standard real Gaussian entries, and set $H_{k,n}=\mathrm{haf}(X^\top X)$.
Its exact second moment and the coefficient in the interval bound are

$$
\sigma_{k,n}^2=\mathbb E H_{k,n}^2
=(2n-1)!!\prod_{q=0}^{n-1}(k+2q),
\qquad
B_{k,n}=\sqrt{\frac2\pi}\,\sigma_{k,n}
\prod_{j=0}^{n-1}\gamma_{k-j}\prod_{r=2}^{n}\gamma_{2r-1}.
$$

The law has a bounded continuous density $f_{k,n}$, with

$$
\sup_x f_{k,n}(x)=f_{k,n}(0)\le\frac{B_{k,n}}{2\sigma_{k,n}}.
$$

For every $z\in\mathbb R$ and $\varepsilon\ge0$,

$$
\Pr\{|H_{k,n}-z|\le\varepsilon\sigma_{k,n}\}
\le\min\{1,B_{k,n}\varepsilon\}.
$$

Under the additional condition $k\ge n+2$,

$$
B_{k,n}\le\frac2{\sqrt\pi}\,n^{3/8}
\exp\!\left(\frac{3n^2+n}{4(k-n-1)}\right).
$$

### Theorem 2.3: symmetric Gaussian hafnians

Let $n\ge1$, and let $W$ be symmetric with independent standard real Gaussian
entries above the diagonal. The diagonal is set to zero; it does not enter the
hafnian. Put

$$
H_n=\mathrm{haf}(W),\qquad
\sigma_n=\sqrt{(2n-1)!!},\qquad
b_n=\sqrt{\frac2\pi}\,\sigma_n\prod_{r=2}^{n}\gamma_{2r-1}.
$$

The second moment is $\mathbb E H_n^2=\sigma_n^2$. At fixed $n$,
$k^{-n/2}H_{k,n}$ converges in distribution to $H_n$,
$k^{-n/2}\sigma_{k,n}\to\sigma_n$, and $B_{k,n}\to b_n$.
The normalized variable $H_n/\sigma_n$ has a continuous even density $p_n$ with

$$
0\le p_n(x)\le p_n(0)\le b_n/2\le n^{3/8}/\sqrt\pi.
$$

For every $z\in\mathbb R$ and $\varepsilon\ge0$,

$$
\Pr\{|H_n-z|\le\varepsilon\sigma_n\}
\le\min\{1,b_n\varepsilon\}
\le\min\{1,(2/\sqrt\pi)n^{3/8}\varepsilon\}.
$$

Empty products equal one. The complete Lean specifications are in
[Challenge.lean](Challenge.lean); this file contains definitions, not assumed
theorems or proof placeholders.

| Paper result | Public Lean theorem |
| --- | --- |
| Theorem 2.1 | [`RealGramHafnians.theorem2_1`](RealGramHafnians.lean) |
| Theorem 2.3 | [`RealGramHafnians.theorem2_3`](RealGramHafnians.lean) |

## Building and verification

Install Git and [elan](https://github.com/leanprover/elan), Lean's toolchain
manager. Download and extract the repository ZIP, or clone the repository.
In a terminal opened in the extracted directory containing `lakefile.toml`, run:

```sh
lake exe cache get
lake build
lake env lean Verification.lean
```

The first command downloads the precompiled mathlib dependencies. The second
builds the proofs and the axiom audit. The last command reruns the audit and
prints the transitive axiom dependencies of both public theorems. It fails if
either theorem depends on any axiom beyond the three standard foundations
listed above. A successful run prints `PASS` for both theorems.

The release was checked on 6 September 2026: the full build succeeded, and both
public theorems reported exactly those three standard foundations.

The versions are pinned for reproducibility:

| Component | Version |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0-rc2` |
| mathlib | `641fbd329d4ffb62bef83c51f54088469056bd36` |

Keep `lean-toolchain` and `lake-manifest.json` unchanged when reproducing the
release. The first build requires internet access and compiles a substantial
local probability library. To reduce simultaneous compiler work, set
`LEAN_NUM_THREADS=2` before building.

## Numerical inputs

No numerical input certificate, simulation, or floating-point computation is
needed. The constants and inequalities are proved symbolically in Lean. This
release does not assume the Pfaffian product law used in a separate comparison
in the paper.

## Source organization and scope

- [RealGramHafnians.lean](RealGramHafnians.lean): the two public proofs.
- [Challenge.lean](Challenge.lean): their full proposition-valued statements.
- [Verification.lean](Verification.lean): enforced transitive axiom checks.
- [RealGramHafnians/Proofs/](RealGramHafnians/Proofs/): the retained paper proofs.
- [LogdetLean/](LogdetLean/): the author's supporting Gaussian, matrix,
  probability, and hafnian development, retaining its original namespaces.
- [lakefile.toml](lakefile.toml), [lake-manifest.json](lake-manifest.json), and
  [lean-toolchain](lean-toolchain): the reproducible build configuration.

The paper includes further comparisons and applications. This GitHub edition
claims verification of the two headline results only; it is not a claim that
every statement in the paper is formalized. The broader companion software is
identified by [Zenodo DOI 10.5281/zenodo.22498111](https://doi.org/10.5281/zenodo.22498111).

## License

Copyright (c) 2026 Hongru Zhao. This edition is licensed under
[Apache License 2.0](LICENSE), matching the license used by
[OpenAI's PrimeGaps186 example](https://github.com/openai/PrimeGaps186).
External dependencies retain their own licenses.
