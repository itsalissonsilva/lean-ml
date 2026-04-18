import LeanML.Init
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
  LeanML.Foundations.Losses.Basic
  Shared pointwise and empirical loss definitions for supervised learning.
-/

open scoped BigOperators

set_option autoImplicit false

namespace LeanML.Foundations.Losses

variable {n : ℕ}
variable {α β : Type*}

/-- Pointwise residual `prediction - target`. -/
def residual (prediction target : ℝ) : ℝ :=
  prediction - target

/-- Sum of a pointwise loss over a finite sample indexed by `Fin n`. -/
noncomputable def empiricalLoss
    (pointLoss : α → β → ℝ)
    (prediction : Fin n → α)
    (target : Fin n → β) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => pointLoss (prediction i) (target i))

/-- Mean pointwise loss over a finite sample indexed by `Fin n`. -/
noncomputable def meanLoss
    (pointLoss : α → β → ℝ)
    (prediction : Fin n → α)
    (target : Fin n → β) : ℝ :=
  empiricalLoss pointLoss prediction target / n

lemma empiricalLoss_nonneg
    (pointLoss : α → β → ℝ)
    (hpoint : ∀ a b, 0 ≤ pointLoss a b)
    (prediction : Fin n → α)
    (target : Fin n → β) :
    0 ≤ empiricalLoss pointLoss prediction target := by
  classical
  unfold empiricalLoss
  refine Finset.induction_on (s := (Finset.univ : Finset (Fin n))) ?base ?step
  · simp
  · intro a s ha hs
    have hnonneg : 0 ≤ pointLoss (prediction a) (target a) :=
      hpoint (prediction a) (target a)
    simpa [Finset.sum_insert, ha] using add_nonneg hnonneg hs

end LeanML.Foundations.Losses

end LeanML.Foundations.Losses
