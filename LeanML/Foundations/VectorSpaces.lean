import LeanML.Init

/-!
  LeanML.Foundations.VectorSpaces
  Finite linear combinations and centroids for vector-valued data.
-/

open scoped BigOperators

set_option autoImplicit false

namespace LeanML.Foundations.VectorSpaces

variable {n : ℕ}
variable {K E : Type*} [Semiring K] [AddCommMonoid E] [Module K E]

/-- A finite linear combination of vectors indexed by `Fin n`. -/
def linearCombination (weights : Fin n → K) (vectors : Fin n → E) : E :=
  (Finset.univ : Finset (Fin n)).sum (fun i => weights i • vectors i)

lemma linearCombination_zero_weights (vectors : Fin n → E) :
    linearCombination (fun _ : Fin n => (0 : K)) vectors = 0 := by
  simp [linearCombination]

lemma linearCombination_zero_vectors (weights : Fin n → K) :
    linearCombination weights (fun _ : Fin n => (0 : E)) = 0 := by
  simp [linearCombination]

lemma linearCombination_add_weights
    (weights weights' : Fin n → K)
    (vectors : Fin n → E) :
    linearCombination (fun i => weights i + weights' i) vectors =
      linearCombination weights vectors + linearCombination weights' vectors := by
  simp [linearCombination, add_smul, Finset.sum_add_distrib]

lemma linearCombination_add_vectors
    (weights : Fin n → K)
    (vectors vectors' : Fin n → E) :
    linearCombination weights (fun i => vectors i + vectors' i) =
      linearCombination weights vectors + linearCombination weights vectors' := by
  simp [linearCombination, smul_add, Finset.sum_add_distrib]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The centroid, or arithmetic mean vector, of a finite sample. -/
noncomputable def centroid (vectors : Fin n → V) : V :=
  linearCombination (fun _ : Fin n => ((n : ℝ)⁻¹)) vectors

lemma centroid_eq_linearCombination (vectors : Fin n → V) :
    centroid vectors =
      linearCombination (fun _ : Fin n => ((n : ℝ)⁻¹)) vectors := by
  rfl

lemma centroid_zero :
    centroid (n := n) (fun _ : Fin n => (0 : V)) = 0 := by
  simp [centroid, linearCombination]

lemma centroid_add (vectors vectors' : Fin n → V) :
    centroid (fun i => vectors i + vectors' i) =
      centroid vectors + centroid vectors' := by
  unfold centroid
  exact linearCombination_add_vectors
    (weights := fun _ : Fin n => ((n : ℝ)⁻¹))
    (vectors := vectors)
    (vectors' := vectors')

end LeanML.Foundations.VectorSpaces
