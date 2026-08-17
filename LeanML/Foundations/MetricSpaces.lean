import LeanML.Init
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
  LeanML.Foundations.MetricSpaces
  Basic metric-space losses and finite-sample aggregate losses.
-/

open scoped BigOperators

set_option autoImplicit false

namespace LeanML.Foundations.MetricSpaces

variable {n : ℕ}
variable {α : Type*}

/-- Metric distance as a pointwise loss. -/
def metricLoss [PseudoMetricSpace α] (prediction target : α) : ℝ :=
  dist prediction target

/-- Squared metric distance as a pointwise loss. -/
def squaredMetricLoss [PseudoMetricSpace α] (prediction target : α) : ℝ :=
  dist prediction target ^ 2

/-- Sum of metric distances over a finite sample indexed by `Fin n`. -/
noncomputable def empiricalMetricLoss
    [PseudoMetricSpace α]
    (prediction target : Fin n → α) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum
    (fun i => metricLoss (prediction i) (target i))

/-- Sum of squared metric distances over a finite sample indexed by `Fin n`. -/
noncomputable def empiricalSquaredMetricLoss
    [PseudoMetricSpace α]
    (prediction target : Fin n → α) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum
    (fun i => squaredMetricLoss (prediction i) (target i))

lemma metricLoss_nonneg [PseudoMetricSpace α] (prediction target : α) :
    0 ≤ metricLoss prediction target := by
  unfold metricLoss
  exact dist_nonneg

lemma metricLoss_self [PseudoMetricSpace α] (x : α) :
    metricLoss x x = 0 := by
  simp [metricLoss]

lemma metricLoss_comm [PseudoMetricSpace α] (x y : α) :
    metricLoss x y = metricLoss y x := by
  simp [metricLoss, dist_comm]

lemma metricLoss_triangle [PseudoMetricSpace α] (x y z : α) :
    metricLoss x z ≤ metricLoss x y + metricLoss y z := by
  simpa [metricLoss] using dist_triangle x y z

lemma squaredMetricLoss_nonneg [PseudoMetricSpace α] (prediction target : α) :
    0 ≤ squaredMetricLoss prediction target := by
  unfold squaredMetricLoss
  exact sq_nonneg (dist prediction target)

lemma squaredMetricLoss_self [PseudoMetricSpace α] (x : α) :
    squaredMetricLoss x x = 0 := by
  simp [squaredMetricLoss]

lemma squaredMetricLoss_comm [PseudoMetricSpace α] (x y : α) :
    squaredMetricLoss x y = squaredMetricLoss y x := by
  simp [squaredMetricLoss, dist_comm]

lemma empiricalMetricLoss_nonneg
    [PseudoMetricSpace α]
    (prediction target : Fin n → α) :
    0 ≤ empiricalMetricLoss prediction target := by
  classical
  unfold empiricalMetricLoss
  refine Finset.induction_on (s := (Finset.univ : Finset (Fin n))) ?base ?step
  · simp
  · intro a s ha hs
    have hnonneg : 0 ≤ metricLoss (prediction a) (target a) :=
      metricLoss_nonneg (prediction a) (target a)
    simpa [Finset.sum_insert, ha] using add_nonneg hnonneg hs

lemma empiricalSquaredMetricLoss_nonneg
    [PseudoMetricSpace α]
    (prediction target : Fin n → α) :
    0 ≤ empiricalSquaredMetricLoss prediction target := by
  classical
  unfold empiricalSquaredMetricLoss
  refine Finset.induction_on (s := (Finset.univ : Finset (Fin n))) ?base ?step
  · simp
  · intro a s ha hs
    have hnonneg : 0 ≤ squaredMetricLoss (prediction a) (target a) :=
      squaredMetricLoss_nonneg (prediction a) (target a)
    simpa [Finset.sum_insert, ha] using add_nonneg hnonneg hs

lemma empiricalMetricLoss_self
    [PseudoMetricSpace α]
    (prediction : Fin n → α) :
    empiricalMetricLoss prediction prediction = 0 := by
  classical
  unfold empiricalMetricLoss metricLoss
  simp

lemma empiricalSquaredMetricLoss_self
    [PseudoMetricSpace α]
    (prediction : Fin n → α) :
    empiricalSquaredMetricLoss prediction prediction = 0 := by
  classical
  unfold empiricalSquaredMetricLoss squaredMetricLoss
  simp

variable {E : Type*} [NormedAddCommGroup E]

/-- The distance induced by a normed additive group. -/
def normDistance (x y : E) : ℝ :=
  ‖x - y‖

lemma normDistance_eq_dist (x y : E) :
    normDistance x y = dist x y := by
  simpa [normDistance] using (dist_eq_norm x y).symm

lemma dist_eq_normDistance (x y : E) :
    dist x y = normDistance x y := by
  simpa [normDistance] using dist_eq_norm x y

lemma normDistance_nonneg (x y : E) :
    0 ≤ normDistance x y := by
  unfold normDistance
  exact norm_nonneg (x - y)

lemma normDistance_self (x : E) :
    normDistance x x = 0 := by
  simp [normDistance]

lemma normDistance_comm (x y : E) :
    normDistance x y = normDistance y x := by
  simp [normDistance, norm_sub_rev]

lemma normDistance_triangle (x y z : E) :
    normDistance x z ≤ normDistance x y + normDistance y z := by
  simpa [normDistance_eq_dist] using
    (metricLoss_triangle (α := E) x y z)

end LeanML.Foundations.MetricSpaces
