import LeanML.Foundations.Losses.Basic
import Mathlib.Data.Real.Basic

/-!
  LeanML.Foundations.Losses.Squared
  Squared-error pointwise and empirical losses.
-/

set_option autoImplicit false

namespace LeanML.Foundations.Losses

variable {n : ℕ}

/-- Squared error at one sample. -/
def squaredError (prediction target : ℝ) : ℝ :=
  residual prediction target ^ 2

/-- Empirical squared loss between predictions and targets. -/
noncomputable def squaredLoss (prediction target : Fin n → ℝ) : ℝ :=
  empiricalLoss squaredError prediction target

lemma squaredError_nonneg (prediction target : ℝ) : 0 ≤ squaredError prediction target := by
  unfold squaredError residual
  exact sq_nonneg (prediction - target)

lemma squaredLoss_nonneg (prediction target : Fin n → ℝ) : 0 ≤ squaredLoss prediction target := by
  unfold squaredLoss
  exact empiricalLoss_nonneg squaredError squaredError_nonneg prediction target

end LeanML.Foundations.Losses
