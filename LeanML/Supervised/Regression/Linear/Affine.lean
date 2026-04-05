/- Copyright (c) 2026 Alisson Matheus Silva. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alisson Matheus Silva -/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false

namespace LeanML.Supervised.Regression.Linear.Affine

variable {n : ℕ}

/-- `Sxx = ∑ xᵢ²`. -/
noncomputable def Sxx (x : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => (x i) ^ 2)

/-- `Sx = ∑ xᵢ`. -/
noncomputable def Sx (x : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => x i)

/-- `Sy = ∑ yᵢ`. -/
noncomputable def Sy (y : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => y i)

/-- `Sxy = ∑ xᵢ yᵢ`. -/
noncomputable def Sxy (x y : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => x i * y i)

/-- The determinant of the normal equations matrix: `Δ = n · Sxx - (Sx)²`. -/
noncomputable def Δ (x : Fin n → ℝ) : ℝ :=
  (n : ℝ) * Sxx x - (Sx x) ^ 2

/-- Optimal slope: `a* = (n · Sxy - Sx · Sy) / Δ`. -/
noncomputable def aStar (x y : Fin n → ℝ) : ℝ :=
  ((n : ℝ) * Sxy x y - Sx x * Sy y) / Δ x

/-- Optimal intercept: `b* = (Sxx · Sy - Sx · Sxy) / Δ`. -/
noncomputable def bStar (x y : Fin n → ℝ) : ℝ :=
  (Sxx x * Sy y - Sx x * Sxy x y) / Δ x

/-- Squared loss: `loss(a, b) = ∑ (a xᵢ + b - yᵢ)²`. -/
noncomputable def loss (x y : Fin n → ℝ) (a b : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => (a * x i + b - y i) ^ 2)

private lemma card_fin_n : (Finset.univ : Finset (Fin n)).card = n :=
  Finset.card_fin n

/-- Helper: `∑ (const) = n * const`. -/
private lemma sum_const_eq (c : ℝ) :
    (Finset.univ : Finset (Fin n)).sum (fun _ => c) = (n : ℝ) * c := by
  simp [Finset.sum_const]

lemma crossTerm_x_eq_zero (x y : Fin n → ℝ) (h : Δ x ≠ 0) :
    (Finset.univ : Finset (Fin n)).sum
        (fun i => x i * (aStar x y * x i + bStar x y - y i)) = 0 := by
  classical
  have hrewrite :
      (Finset.univ : Finset (Fin n)).sum
          (fun i => x i * (aStar x y * x i + bStar x y - y i))
        =
      aStar x y * Sxx x + bStar x y * Sx x - Sxy x y := by
    have h1 :
        (Finset.univ : Finset (Fin n)).sum
            (fun i => x i * (aStar x y * x i + bStar x y - y i))
          =
        (Finset.univ : Finset (Fin n)).sum
            (fun i => aStar x y * (x i) ^ 2 + bStar x y * x i - x i * y i) := by
      refine Finset.sum_congr rfl ?_
      intro i _; ring_nf
    rw [h1]
    have h2 :=
      Finset.sum_sub_distrib
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => aStar x y * (x i) ^ 2 + bStar x y * x i)
        (g := fun i => x i * y i)
    rw [h2]
    have h3 :=
      Finset.sum_add_distrib
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => aStar x y * (x i) ^ 2)
        (g := fun i => bStar x y * x i)
    rw [h3]
    have hm1 :=
      (Finset.mul_sum
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => (x i) ^ 2)
        (a := aStar x y)).symm
    have hm2 :=
      (Finset.mul_sum
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => x i)
        (a := bStar x y)).symm
    rw [hm1, hm2]
    simp [Sxx, Sx, Sxy]
  rw [hrewrite]
  simp only [aStar, bStar, Δ] at h ⊢
  field_simp
  ring

lemma crossTerm_const_eq_zero (x y : Fin n → ℝ) (h : Δ x ≠ 0) :
    (Finset.univ : Finset (Fin n)).sum
        (fun i => aStar x y * x i + bStar x y - y i) = 0 := by
  classical
  have hrewrite :
      (Finset.univ : Finset (Fin n)).sum
          (fun i => aStar x y * x i + bStar x y - y i)
        =
      aStar x y * Sx x + (n : ℝ) * bStar x y - Sy y := by
    have h1 :=
      Finset.sum_sub_distrib
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => aStar x y * x i + bStar x y)
        (g := fun i => y i)
    rw [h1]
    have h2 :=
      Finset.sum_add_distrib
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => aStar x y * x i)
        (g := fun _ => bStar x y)
    rw [h2]
    have hm :=
      (Finset.mul_sum
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => x i)
        (a := aStar x y)).symm
    rw [hm]
    have hc := sum_const_eq (n := n) (bStar x y)
    rw [hc]
    simp [Sx, Sy]
  rw [hrewrite]
  simp only [aStar, bStar, Δ] at h ⊢
  field_simp
  ring

private lemma quad_eq_sum_sq (x : Fin n → ℝ) (u v : ℝ) :
    Sxx x * u ^ 2 + 2 * Sx x * u * v + (n : ℝ) * v ^ 2
      =
    (Finset.univ : Finset (Fin n)).sum (fun i => (u * x i + v) ^ 2) := by
  classical
  have hexp :
      (Finset.univ : Finset (Fin n)).sum (fun i => (u * x i + v) ^ 2)
        =
      (Finset.univ : Finset (Fin n)).sum
          (fun i => u ^ 2 * (x i) ^ 2 + 2 * u * v * x i + v ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro i _; ring
  rw [hexp]
  have h1 :=
    Finset.sum_add_distrib
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => u ^ 2 * (x i) ^ 2 + 2 * u * v * x i)
      (g := fun _ => v ^ 2)
  rw [h1]
  have h2 :=
    Finset.sum_add_distrib
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => u ^ 2 * (x i) ^ 2)
      (g := fun i => 2 * u * v * x i)
  rw [h2]
  have hm1 :=
    (Finset.mul_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => (x i) ^ 2)
      (a := u ^ 2)).symm
  have hm2 :=
    (Finset.mul_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => x i)
      (a := 2 * u * v)).symm
  rw [hm1, hm2]
  have hc := sum_const_eq (n := n) (v ^ 2)
  rw [hc]
  simp [Sxx, Sx]
  ring

lemma quad_form_nonneg (x : Fin n → ℝ) (u v : ℝ) :
    0 ≤ Sxx x * u ^ 2 + 2 * Sx x * u * v + (n : ℝ) * v ^ 2 := by
  rw [quad_eq_sum_sq]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

lemma loss_decomp (x y : Fin n → ℝ) (h : Δ x ≠ 0) (a b : ℝ) :
    loss x y a b =
      loss x y (aStar x y) (bStar x y)
        + Sxx x * (a - aStar x y) ^ 2
        + 2 * Sx x * (a - aStar x y) * (b - bStar x y)
        + (n : ℝ) * (b - bStar x y) ^ 2 := by
  classical
  let a0 := aStar x y
  let b0 := bStar x y
  let da := a - a0
  let db := b - b0
  -- Each residual splits
  have hterm : ∀ i : Fin n,
      a * x i + b - y i = (da * x i + db) + (a0 * x i + b0 - y i) := by
    intro i; simp [da, db, a0, b0]; ring
  -- Cross terms vanish
  have hcross_x :
      (Finset.univ : Finset (Fin n)).sum
          (fun i => x i * (a0 * x i + b0 - y i)) = 0 :=
    crossTerm_x_eq_zero x y h
  have hcross_c :
      (Finset.univ : Finset (Fin n)).sum
          (fun i => (a0 * x i + b0 - y i)) = 0 :=
    crossTerm_const_eq_zero x y h
  -- Expand (p + q)² = p² + q² + 2pq
  have hexpand :
      (Finset.univ : Finset (Fin n)).sum (fun i => (a * x i + b - y i) ^ 2)
        =
      (Finset.univ : Finset (Fin n)).sum (fun i =>
          (da * x i + db) ^ 2
          + (a0 * x i + b0 - y i) ^ 2
          + 2 * (da * x i + db) * (a0 * x i + b0 - y i)) := by
    refine Finset.sum_congr rfl ?_
    intro i _; rw [hterm i]; ring
  -- Split the sum of three terms
  have hsplit :
      (Finset.univ : Finset (Fin n)).sum (fun i =>
          (da * x i + db) ^ 2
          + (a0 * x i + b0 - y i) ^ 2
          + 2 * (da * x i + db) * (a0 * x i + b0 - y i))
        =
      (Finset.univ : Finset (Fin n)).sum (fun i => (da * x i + db) ^ 2)
        + (Finset.univ : Finset (Fin n)).sum (fun i => (a0 * x i + b0 - y i) ^ 2)
        + (Finset.univ : Finset (Fin n)).sum
            (fun i => 2 * (da * x i + db) * (a0 * x i + b0 - y i)) := by
    have := Finset.sum_add_distrib
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => (da * x i + db) ^ 2 + (a0 * x i + b0 - y i) ^ 2)
      (g := fun i => 2 * (da * x i + db) * (a0 * x i + b0 - y i))
    have := Finset.sum_add_distrib
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => (da * x i + db) ^ 2)
      (g := fun i => (a0 * x i + b0 - y i) ^ 2)
    linarith
  -- The cross sum vanishes
  have hcross_sum :
      (Finset.univ : Finset (Fin n)).sum
          (fun i => 2 * (da * x i + db) * (a0 * x i + b0 - y i)) = 0 := by
    have hcong :
        (Finset.univ : Finset (Fin n)).sum
            (fun i => 2 * (da * x i + db) * (a0 * x i + b0 - y i))
          =
        (Finset.univ : Finset (Fin n)).sum
            (fun i => 2 * da * (x i * (a0 * x i + b0 - y i))
              + 2 * db * ((a0 * x i + b0 - y i))) := by
      refine Finset.sum_congr rfl ?_
      intro i _; ring
    rw [hcong]
    have h_add :=
      Finset.sum_add_distrib
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => 2 * da * (x i * (a0 * x i + b0 - y i)))
        (g := fun i => 2 * db * ((a0 * x i + b0 - y i)))
    rw [h_add]
    have hm1 :=
      (Finset.mul_sum
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => x i * (a0 * x i + b0 - y i))
        (a := 2 * da)).symm
    have hm2 :=
      (Finset.mul_sum
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => (a0 * x i + b0 - y i))
        (a := 2 * db)).symm
    rw [hm1, hm2, hcross_x, hcross_c]
    ring
  -- The perturbation is a quadratic form
  have hquad :
      (Finset.univ : Finset (Fin n)).sum (fun i => (da * x i + db) ^ 2)
        =
      Sxx x * da ^ 2 + 2 * Sx x * da * db + (n : ℝ) * db ^ 2 := by
    have := (quad_eq_sum_sq x da db).symm
    linarith
  -- Assemble
  unfold loss
  linarith [hexpand, hsplit, hcross_sum, hquad]

/-- `(aStar, bStar)` minimizes the squared loss (affine regression). -/
theorem optimal_minimizes (x y : Fin n → ℝ) (hΔ : 0 < Δ x) :
    ∀ a b : ℝ, loss x y (aStar x y) (bStar x y) ≤ loss x y a b := by
  intro a b
  have h : Δ x ≠ 0 := ne_of_gt hΔ
  have hdecomp := loss_decomp x y h a b
  have hnonneg := quad_form_nonneg x (a - aStar x y) (b - bStar x y)
  linarith

end LeanML.Supervised.Regression.Linear.Affine
