# Formalization layer (`formalization/`)

This directory holds the **abstract formalization layer** of the research note
*Research Notes on ζ(9): Constructions, Computations, and Open Problems* (v0.1).

**Scope boundary.** None of the statements below mentions ζ(9) or any other specific
number. They are general-purpose lemmas — irrationality criteria from small integer
linear forms, moment-matching quadrature exactness, sign-forcing nonvanishing,
Taylor-kernel positivity, and supporting positivity inequalities. Formalizing them is
**not** a step toward a proof of the irrationality of ζ(9), and this directory makes no
claim about ζ(9).

## Contents

| file | what it is |
|---|---|
| `Zeta9Note.lean` | all eight theorems in one self-contained file, namespace `Zeta9Note` |
| `docs/statements/` | natural-language statements (as published with each platform item) |
| `docs/explanations/` | explanations and explicit scope limits for each proof |

## The eight theorems

| # | theorem | kind |
|---|---|---|
| 1 | `quadrature_exact_of_moments` | moment matching ⇒ exact quadrature up to degree 4 |
| 2 | `min_lt_weighted_average_lt_max` | weighted average strictly between min and max |
| 3 | `mediant_strictly_between_min_and_max` | mediant inequality (reduces to 2) |
| 4 | `positive_matrix_maps_nonneg_to_pos` | positive matrix maps nonzero nonneg vectors to positive |
| 5 | `taylor_sign_implies_kernel_sum_pos` | nonnegative Taylor coefficients ⇒ positive kernel sum |
| 6 | `five_sample_sign_forces_nonzero` | sign at five nodes forces `L p ≠ 0` (reduces to 1) |
| 7 | `irrational_of_small_nonzero_integer_forms` | one-form irrationality criterion |
| 8 | `irrational_of_two_small_integer_forms` | two-form (independent) irrationality criterion |

## Toolchain and how to reproduce

The file was checked with Lean **4.33.1** against Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`. This repository has no Lake project of its
own yet; the file was compiled from a workspace that provides that Mathlib build:

```bash
lake env lean formalization/Zeta9Note.lean
# expected: no output, exit code 0 (no sorry, no warnings)
```

A standalone Lake project is planned for a later version.

## Provenance and naming

These statements and proofs mirror the items of the public prove2.me mission
*Formalize the abstract layer of "Research Notes on ζ(9)" (v0.1)*, published under the
namespace `Zeta9Note`. A separate private mission carries the ζ(9)-specific items under
a different namespace (`ZetaNine`); its obligations — which do mention `riemannZeta` —
are deliberately **not** included here.

## License

Original software files here are licensed under the **MIT License** (see
`../LICENSES/MIT.txt`); the accompanying documentation is **CC BY 4.0**.
