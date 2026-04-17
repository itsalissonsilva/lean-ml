# Contributing to LeanML

Thanks for your interest in contributing! Here's how to get started.

## Setup

1. Install Lean 4 via [elan](https://github.com/leanprover/elan)
2. Clone the repo and build:

```bash
git clone https://github.com/itsalissonsilva/lean-ml.git
cd lean-ml
lake update
lake exe cache get
lake build
```

## What to work on

Check the README for algorithms marked as TBD. Some good first contributions:

- **Regression.Ridge:** Very close to the existing Origin/Affine proofs, just add an L2 penalty term.
- **Classification.Logistic:** Convex loss, unique minimum. Needs Mathlib's `Real.exp` and `Real.log`.
- **Bayes.NaiveBayes:** Probabilistic, would need Mathlib's measure theory basics.
- **Foundations/Optimization:** Helper lemmas for convexity, gradient properties, etc.

If you're unsure where to start, open an issue and we can figure it out together.

## Code style

- Use `(Finset.univ : Finset (Fin n)).sum (fun i => ...)` for finite sums (not `∑ i` shorthand) to avoid syntactic mismatches with `Finset.mul_sum` and `Finset.sum_add_distrib`.
- Mark definitions as `noncomputable` when working over `ℝ`.
- Set `set_option autoImplicit false` at the top of each file.
- Use the namespace pattern `LeanML.Module.Submodule.Name`.
- Keep proofs explicit. Prefer `calc` blocks and named `have` steps over long tactic chains.

## Submitting changes

1. Fork the repo
2. Create a branch (`git checkout -b my-feature`)
3. Make sure `lake build` passes with no errors
4. Open a pull request with a description of what you proved and the proof strategy

## License

By contributing you agree that your work will be licensed under Apache 2.0.
