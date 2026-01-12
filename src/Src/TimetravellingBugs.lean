import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Basic   -- gives complement on Finset

open LinearMap (BilinForm)
open Module

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (b : BilinForm K E) (hb : b.IsSymm)
variable {n : Type*} [Fintype n] (v : Basis n K E) (b : BilinForm K E)

-- define set of basis vectors that lie in the kernel
variable [DecidablePred fun i : n => b (v i) (v i) = 0]
def A : Finset n :=  Finset.univ.filter (fun i => b (v i) (v i) = 0)

lemma ker_imp_nullform
    (hb : b.IsSymm) (ortho : b.iIsOrtho v) :
    ∀ i, b (v i) (v i) = 0 → b (v i) = 0 := by
      sorry

lemma kernel_imp_nonkernel_basis_coeff_zero
    (w : E) (hw : w ∈ LinearMap.ker b) (ortho : b.iIsOrtho v) (hb : b.IsSymm) :
    ∀ i, i ∉ A v b → (v.repr w) i = (0 : K) := by
  intro i hi
  simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  push_neg at hi
  have h : b (v i) ≠ 0 := by
    intro h₀
    rw [h₀] at hi
    simp only [LinearMap.zero_apply, ne_eq, not_true_eq_false] at hi
  have hw0 : b w = 0 := LinearMap.mem_ker.mp hw
  have w_eq : ∑ i , (v.repr w) i • v i = w :=  v.sum_repr w
  apply congr_arg b at w_eq
  rw [map_sum b] at w_eq
  simp only [map_smul] at w_eq
  rw [hw0] at w_eq
  set B : Finset n := (Finset.univ : Finset n).filter (fun i => b (v i) (v i) ≠ 0)
  have hB : B ⊆ Finset.univ := by simp
  rw [← Finset.sum_subset hB _] at w_eq
  swap
  · simp [B]
    intro j hj
    apply ker_imp_nullform _ _ hb ortho at hj
    right
    assumption'
  · simp at hB
    let apply_vi := congr_arg (fun φ => φ (v i)) w_eq
    simp at apply_vi
    have hᵢ : i ∈ B := by
      simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, hi, not_false_eq_true, and_self, B]
    have hx : ∀ x ∈ B, x ≠ i → (v.repr w) x * (b (v x)) (v i) = 0 := by
      intro x hxB x_ne_i
      simp only [LinearMap.BilinForm.iIsOrtho_def.mp ortho x i x_ne_i, mul_zero]
    rw [Finset.sum_eq_single i hx] at apply_vi
    · exact (mul_eq_zero_iff_right hi).mp apply_vi
    exact fun a ↦ hx i hᵢ fun a_1 ↦ a hᵢ

lemma kernel_imp_nonkernel_basis_coeff_zero'
    (w : E) (hw : w ∈ LinearMap.ker b) (ortho : b.iIsOrtho v) (hb : b.IsSymm) :
    ∀ i, i ∉ A v b → (v.repr w) i = (0 : K) := by
  intro i hi
  simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  push_neg at hi
  have h : b (v i) ≠ 0 := by
    intro h₀
    rw [h₀] at hi
    simp only [LinearMap.zero_apply, ne_eq, not_true_eq_false] at hi
  have hw0 : b w = 0 := LinearMap.mem_ker.mp hw
  have w_eq : ∑ i , (v.repr w) i • v i = w :=  v.sum_repr w
  apply congr_arg b at w_eq
  rw [map_sum b] at w_eq
  simp only [map_smul] at w_eq
  rw [hw0] at w_eq
  set B : Finset n := (Finset.univ : Finset n).filter (fun i => b (v i) (v i) ≠ 0)
  have hB : B ⊆ Finset.univ := by simp
  rw [← Finset.sum_subset hB _] at w_eq
  swap
  · simp [B]
    intro j hj
    apply ker_imp_nullform _ _ _ at hj
    right
    assumption'
  · simp at hB
    let apply_vi := congr_arg (fun φ => φ (v i)) w_eq
    simp at apply_vi
    have hᵢ : i ∈ B := by
      simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, hi, not_false_eq_true, and_self, B]
    have hx : ∀ x ∈ B, x ≠ i → (v.repr w) x * (b (v x)) (v i) = 0 := by
      intro x hxB x_ne_i
      simp only [LinearMap.BilinForm.iIsOrtho_def.mp ortho x i x_ne_i, mul_zero]
    rw [Finset.sum_eq_single i hx] at apply_vi
    · exact (mul_eq_zero_iff_right hi).mp apply_vi
    exact fun a ↦ hx i hᵢ fun a_1 ↦ a hᵢ

