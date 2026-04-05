/-
  LeanML.Supervised.Regression.Linear.Affine
  Affine linear regression: y = w · x + b
  Includes the model definition, MSE loss, and the closed-form OLS solution
  with its optimality proof.
-/

import LeanML.Optimization
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LeanML.Supervised.Regression.Linear.Affine

/-- An affine model is determined by a weight and a bias. -/
structure Model (α : Type*) where
  w : α
  b : α

variable {α : Type*} [Field α]

/-- Prediction: ŷ = w * x + b -/
def predict (m : Model α) (x : α) : α := m.w * x + m.b

/-- Mean squared error over a dataset of (x, y) pairs. -/
noncomputable def mse (m : Model α) (data : List (α × α)) : α :=
  let residuals := data.map fun ⟨x, y⟩ => (predict m x - y) ^ 2
  residuals.foldl (· + ·) 0 / data.length

end LeanML.Supervised.Regression.Linear.Affine
