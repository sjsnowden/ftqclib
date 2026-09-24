# ftqclib

A Lean 4 and Mathlib formalization of stabilizer and Clifford quantum mechanics as finite symplectic
dynamics over 𝔽₂, extended up the Clifford hierarchy, together with a Mathlib-only library of
higher-order Fourier analysis and coding theory. The default build targets contain no `sorry`, and
the headline theorems depend only on the standard three axioms (`propext`, `Classical.choice`,
`Quot.sound`).

ftqclib continues the Lean code of QECLean, by sjsnowden and SamBosonic.

## Libraries

| library | contents |
|---|---|
| `FTQCLib` | Pauli groups and the symplectic form; stabilizer states and codes (including CSS); the Clifford group as the affine symplectic group; the Cui–Gottesman–Krishna classification of diagonal gates in the Clifford hierarchy; the kernel frame, in which a state is a support coset carrying a phase polynomial over ℤ/2^m, a Clifford gate is a symplectic map and measurement is conditioning on a coset; the Hadamard on both representations with a certificate that they agree; the sign cohomology and metaplectic non-splitting. |
| `ECCLib` | Gowers norms and higher-order Fourier analysis over finite abelian groups; Gauss sums and the Weil representation; Reed–Muller, Reed–Solomon and generalized Reed–Solomon codes; MacWilliams identities, Krawtchouk polynomials and the Delsarte linear-programming bound; association schemes; Berlekamp–Massey and Gao decoding. |

`ECCLib` imports only Mathlib. `FTQCLib` imports `ECCLib` and Mathlib.

## Building

```bash
lake exe cache get
lake build
```

The toolchain is pinned in `lean-toolchain` and Mathlib in `lakefile.toml`. `lake build` builds both
libraries. Check the axioms behind any result with `#print axioms <name>`.

Modules whose name ends in `Check` hold executable checks (`#guard`, `#guard_msgs`, `decide`) of the
module they accompany. Files under `FTQCLib/Explore/` are standalone explorations outside the default
target; build one with `lake build FTQCLib.Explore.<File>`.

## License

Lean source files (`*.lean`) are licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).
Everything else in this repository is copyright Sam Snowden, all rights reserved. See
[`LICENSING.md`](LICENSING.md).
