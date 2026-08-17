import LeanML.Foundations.MetricSpaces
import Mathlib.Data.Real.Basic

/-!
  LeanML.Foundations.NormedSpaces
  Pointwise norm losses for vector-valued models, plus metric compatibility.
-/

set_option autoImplicit false

namespace LeanML.Foundations.NormedSpaces

open LeanML.Foundations.MetricSpaces

variable {E : Type*} [NormedAddCommGroup E]

/-- Norm distance as a pointwise loss for vector-valued predictions. -/
def normLoss (prediction target : E) : ℝ :=
  ‖prediction - target‖

/-- Squared norm distance as a pointwise loss for vector-valued predictions. -/
def squaredNormLoss (prediction target : E) : ℝ :=
  normLoss prediction target ^ 2

lemma normLoss_eq_metricLoss (prediction target : E) :
    normLoss prediction target = metricLoss prediction target := by
  simp [normLoss, metricLoss, dist_eq_norm]

lemma squaredNormLoss_eq_squaredMetricLoss (prediction target : E) :
    squaredNormLoss prediction target = squaredMetricLoss prediction target := by
  simp [squaredNormLoss, squaredMetricLoss, normLoss, dist_eq_norm]

lemma normLoss_nonneg (prediction target : E) :
    0 ≤ normLoss prediction target := by
  unfold normLoss
  exact norm_nonneg (prediction - target)

lemma squaredNormLoss_nonneg (prediction target : E) :
    0 ≤ squaredNormLoss prediction target := by
  unfold squaredNormLoss
  exact sq_nonneg (normLoss prediction target)

lemma normLoss_self (x : E) :
    normLoss x x = 0 := by
  simp [normLoss]

lemma squaredNormLoss_self (x : E) :
    squaredNormLoss x x = 0 := by
  simp [squaredNormLoss, normLoss]

lemma normLoss_comm (x y : E) :
    normLoss x y = normLoss y x := by
  simp [normLoss, norm_sub_rev]

lemma squaredNormLoss_comm (x y : E) :
    squaredNormLoss x y = squaredNormLoss y x := by
  simp [squaredNormLoss, normLoss_comm]

lemma normLoss_triangle (x y z : E) :
    normLoss x z ≤ normLoss x y + normLoss y z := by
  simpa [normLoss, dist_eq_norm] using dist_triangle x y z

end LeanML.Foundations.NormedSpaces
