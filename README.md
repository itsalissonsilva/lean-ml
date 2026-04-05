# LeanML

Formally verified machine learning algorithms in [Lean 4](https://lean-lang.org/) with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

## Structure

* **Foundations:** Vector spaces, norms, inner products
* **Optimization:** Loss functions, convexity, gradient descent
* **Supervised**

  * **Regression.Linear.Origin:** `y = w·x` with OLS optimality proof
  * **Regression.Linear.Affine:** `y = w·x + b` with OLS optimality proof
  * **Regression.Polynomial:** Polynomial regression (TBD)
  * **Regression.Ridge:** L2-regularized regression (TBD)
  * **Classification.Logistic:** Logistic regression (TBD)
  * **Classification.SVM:** Support vector machines (TBD)
  * **Classification.KNN:** K-nearest neighbors (TBD)
* **Unsupervised**

  * **Clustering.KMeans:** K-means clustering (TBD)
  * **DimensionReduction.PCA:** Principal component analysis (TBD)

## Building

```bash
# Install Lean 4 via elan
curl https://elan.lean-lang.org/install.sh -sSf | sh

# Build the project
lake update
lake build
```

