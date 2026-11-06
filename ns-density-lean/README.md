# A density theorem for non-standard irreducible cyclic codes

Lean 4 proofs accompanying the manuscript by Tao Feng, Henk D. L. Hollmann,
Weicong Li and Qing Xiang. The manuscript source is
[`paper/ns-density-paper-arx-subm-2026-10-31.tex`](paper/ns-density-paper-arx-subm-2026-10-31.tex).

For each fixed prime `p`, the project proves that the positive lengths admitting
a non-standard non-degenerate irreducible cyclic code over some finite field of
characteristic `p` have natural density zero. It also proves the exact equality
of this exceptional set with the exceptional set over the prime alphabet, and
the supremum formula in Corollary 1.2.

The result is conditional on two explicitly named mathematical inputs:

- `FHLXOriginalInput PaperNonstandard`: the classification in FHLX Theorem 1.1,
  the five initial families in Examples 3.1–3.5, and preservation by the four
  original constructions in Constructions 3.7–3.10. The density bound uses only
  the forward classification. The original exceptions and hypotheses are retained.
- `WiertelakMoreeInput`: divergence of the reciprocal sum of primes `r` coprime
  to `b` for which `h` divides the order of `b` modulo `r`, for `b,h > 1`.

These inputs are theorem parameters. Neither result is declared as a global
axiom or proved in this repository. No GRH or Artin-conjecture assumption is used.

## Main declarations

The endpoint `NSDensity.abstract_density_main` in
[`AbstractCharacteristic.lean`](NSDensity/AbstractCharacteristic.lean) includes
the union identity, real-cutoff little-o estimate, and relative density one for
simultaneous standardness over all finite fields of characteristic `p`.
The definitions quantify over actual code subspaces and permutation
automorphisms. The representation of an arbitrary nondegenerate irreducible
cyclic code by exact-order roots is proved internally.

`NSDensity.abstractRatio_sup_eq` and
`NSDensity.abstractRatio_sup_tendsto_zero` in
[`AbstractMain.lean`](NSDensity/AbstractMain.lean) give the exact supremum
identity and limit over all positive alphabet exponents.

[`SubmissionAudit.lean`](SubmissionAudit.lean) makes the submission's new
Corollary 3.7 explicit. It proves the exact derived-length characterization and
realization at both the original alphabet and the prime alphabet from the
existing normal form, without either external input.

## Reproduce the checks

The project pins Lean `v4.35.0` and mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` in the toolchain and Lake files.
With Lean/Elan installed, run these commands from the repository root:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean SubmissionAudit.lean
```

The first command downloads the pinned mathlib build cache. The audit commands
print the external-input interfaces, theorem signatures and axiom dependencies.
The main results and submission corollary use only Lean's standard `propext`,
`Classical.choice` and `Quot.sound` logical axioms. There are no `sorry`, `admit`,
custom mathematical axioms or `native_decide` proofs in the project sources.

## Correspondence with the submission

The 31 October manuscript was compared with the existing formalization on
7 November 2026. Its 22 numbered results and one definition are mapped below.
This is a mathematical source correspondence review, not a claim that a TeX
document can itself be checked by Lean.

| Manuscript | Lean counterpart |
| --- | --- |
| Theorem 1.1 | `abstract_density_main` |
| Corollary 1.2 | `abstractRatio_sup_eq`, `abstractRatio_sup_tendsto_zero` |
| Proposition 2.1 | `standardGroup_card`, `standardGroup_eq_closure`, `rootLinearGroupEquiv_permutationAutGroup`, `rootLinearGroupEquiv_standard_iff` |
| Theorem 2.2 | Explicit `FHLXOriginalInput`; original-path equivalence in `FHLXPaper.lean` |
| Definition 3.1 | `Derived`, the reflexive transitive closure of `Step` |
| Proposition 3.2 | Internally proved unrestricted descent; the permitted FHLX preservation results; `normalForm_preserves` |
| Corollary 3.3 | `abstract_prime_power_union_eq_prime` |
| Lemma 3.4 | `extension_iff_mul_dvd_lcm`, `div_gcd_dvd_div_gcd`, `order_extension`, `order_power`; the lcm identity follows from the extension divisibilities |
| Proposition 3.5 | `tensor_derived`, `paper_original_nonstandard_iff_derived` |
| Theorem 3.6 | `derived_iff_normalForm` |
| Corollary 3.7 | `submission_derived_length_iff`, `submission_normalLengths_realized` |
| Lemma 4.1 | `order_dvd_of_modulus_dvd`, `order_le_quotient_mul` |
| Proposition 4.2 | `EquallySpaced.lift`, `.extension`, `.descent`, `.of_derived`, `.of_derived_length_ge_six` |
| Theorem 5.1 | External `WiertelakMoreeInput`, using only the reciprocal-divergence consequence |
| Lemma 5.2 | `densityZero_avoids`, `densityZero_atMostOne` |
| Lemma 5.3 | `densityZero_iUnion_of_reciprocalTails` |
| Proposition 6.1 | `densityZero_normalLengths` |
| Corollary 6.2 | `densityZero_golayLengths` |
| Proposition 6.3 | `densityZero_dualRepetitionLengths` |
| Proposition 6.4 | `densityZero_primitiveLengths`, `densityZero_ovoidLengths` |
| Lemma 6.5 | `equallySpaced_iff_exists_witness`, `ESWitness.square_dvd` |
| Lemma 6.6 | `densityZero_ESFixed` |
| Theorem 6.7 | `densityZero_equallySpaced`, `reciprocalTails_powerGrid` |

The exact multiplier set `AdmissibleMultipliers` retains the quotient by the
gcd, so `NormalLengths n q` is the manuscript's set `n U_{n,q}`. The fixed-pair
sieve uses a prime divisor of the degree in Lean and the whole degree in the
submission; both establish the same required conclusion under the same input.
The normal-form and equally-spaced closure proofs also differ in presentation.

The formalization does not cover every sentence of the manuscript. In particular,
the explanatory degenerate-code and direct-sum discussions, degree-one and
length-four standardness remarks, the complete textbook dictionary for reducible
codes, and literature comparisons are not independently formalized. Some exact
displayed constants and exponential sieve formulas are replaced by sufficient
internally proved bounds. The prime-density theorem and its explanatory analytic
derivation remain outside the kernel proof; only the stated reciprocal divergence
is assumed. These items are not additional premises of the main Lean theorem.

## Verification evidence

- `verification/sources.json` and `verification/build.log` preserve the successful
  28 October full check of the original 55 proof sources, with zero errors and
  zero warnings.
- On 7 November all 55 source hashes and the bound build-log hash were checked
  again and matched. The unchanged original proof files were not relabeled as
  a newly repeated full build.
- `verification/submission-endpoints-20261107.log` records a fresh kernel check
  of `SubmissionAudit.lean`, including the new corollary and main theorem types.
- `verification/submission-review-20261107.json` binds this review to the exact
  manuscript, original source manifest and new submission audit.

Historical source-audit metadata is retained as historical evidence. Its older
manuscript fingerprint does not certify the later submission by itself. The
current submission review supplies that separate correspondence.
