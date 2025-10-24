import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Real.Basic
open LinearMap (BilinForm)
/-!
# Sylvester's Theorem

We're trying to implement sylvester's theorem.
For now, until better ideas strike, we're working against Lang's formulation of the
theorem in terms of symmetric bilinear maps.

-/

/- using selected parts of Lang's chapter XV as exercises -/

variable {k : Type*} [Field k]
 /- actually need ring with 2x ≠ 0 , use ℝ for now.
 integral domains? In the case of fields, char(k) ≠ 2 is sufficient.
 "without 2-torsion" seems to be the term for rings. -/
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (g : BilinForm ℝ V)


/- Alternating forms can be equivalently defined by the following two Props. -/
def alternating : Prop := ∀x y :V, g x y = - (g y x)

def symm_eq_zero : Prop := ∀ x : V, g x x = 0

theorem alternating_of_0 : alternating g → symm_eq_zero g := by
  unfold alternating
  intros Halt x
  specialize Halt x x
  linarith

theorem symm_eq_zero_of_alternating : symm_eq_zero g → alternating g := by
  unfold symm_eq_zero alternating
  intros Hsymm x y
  have Hsymm_sum := Hsymm (x + y) -- annoying that I can't use specialize here, as it destroys the original statement
  simp at Hsymm_sum
  have Hx := Hsymm x
  have Hy := Hsymm y
  rw [Hx, Hy] at Hsymm_sum
  simp at Hsymm_sum
  linarith
  -- rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
  -- LinearMap.BilinForm.add_right] at Hsymm_sum

section Nullform

variable {K : Type*} [Field K] [NeZero (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable (n : BilinForm K V)
variable (hb : n.IsSymm)

def nullform : Prop := ∀x y : V, n x y = 0

example :
    (∀ z : V, n z z = 0) → nullform n := by
  intros H
  unfold nullform
  intros x y
  have Hsum := H (x+y)
  have Hdiff := H (x-y)
  have H4xy := congrArg₂ (· - ·) Hsum Hdiff
  simp at *
  have Hxx0 := H x
  have Hyy0 := H y
  rw [Hxx0, Hyy0] at H4xy
  simp [sub_eq_add_neg] at H4xy
  rw [hb.eq y x] at H4xy
  abel_nf at H4xy
  have H2 : NeZero (2 : K) := inferInstance
  simp at H4xy
  rcases H4xy with ha | hb
  · by_contra
    · have h4 : (4 : K) ≠ 0 := by convert mul_ne_zero H2.ne H2.ne ; norm_num
      contradiction
  · assumption

theorem null_imp_nonnondeg
    [Nontrivial V] [LinearOrder K] [IsStrictOrderedRing K] :
    n = 0 → ¬ n.Nondegenerate := by
  intro hn hnd
  apply LinearMap.BilinForm.Nondegenerate.ne_zero hnd
  assumption


end Nullform


section FinDim


-- field with characteristic ≠ 0
variable {k : Type*} [Field k] [NeZero (2 : k)]
-- vsp over this field
variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]


-- Ordered field
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] -- [NeZero (2 : K)]
-- fin. dim. vsp. over this ordered field
variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]


/- utility class wrapping `LinearMap.BilinForm.IsSymm`.
  Of unclear necessity.
-- variable (b : BilinForm k V)
-- class IsSymm' : Prop where
--   out : IsSymm b
-/


variable (b : BilinForm K E)


/-
  not actually true. consider diagonal form [[1, 0], [0, -1]].
  this is nondegenerate, symmetric, but for every x we have x² = 0.
-- lemma nonzero_of_nondegenerate (x : V) (h : NeZero x) :
-/

variable {n : Type*} [Fintype n]
open Module

theorem square_obasis_nonzero
    {v : Basis n K E} (h : b.iIsOrtho v) (hb : b.Nondegenerate) :
    ∀ i, b (v i) (v i) ≠ 0 := by
  intro i
  have ho : ¬b.IsOrtho (v i) (v i) := by
    apply h.not_isOrtho_basis_self_of_nondegenerate
    assumption
  rw [b.isOrtho_def] at ho
  assumption

theorem nondeg_of_nonnull_basis
    {v : Basis n K E} (ortho : b.iIsOrtho v) (h : ∀ i, b (v i) (v i) ≠ 0) :
    b.Nondegenerate := by
  apply ortho.nondegenerate_iff_not_isOrtho_basis_self.mpr
  simp at h
  intro i
  specialize h i
  intro H
  exact h H

theorem nondeg_iff_nonnull_on_basis
    {v : Basis n K E} (ortho : b.iIsOrtho v) :
    (∀ i, b (v i) (v i) ≠ 0) ↔ b.Nondegenerate := by
  refine ⟨nondeg_of_nonnull_basis (b := b) ortho, ?_⟩
  intro hb
  exact square_obasis_nonzero (b := b) ortho hb

theorem square_obasis_ltzero_or_gtzero
    {v : Basis n K E} (h : b.iIsOrtho v) (hb : b.Nondegenerate) :
    ∀ i, b (v i) (v i) > 0 ∨ b (v i) (v i) < 0 := by
  simp
  intro i
  rw [eq_comm]
  revert i
  exact square_obasis_nonzero b h hb


variable {n : Type*} [Fintype n] (v : Basis n K E) (b : BilinForm K E)

theorem card_selforthogonal_eq_dim_ker
    (h : b.iIsOrtho v) (hb : b.Nondegenerate) :
    (Finset.univ.filter fun i => b (v i) (v i) = 0).card =
      finrank K (LinearMap.ker b) := by
  sorry

theorem span_iselforthogonal_subset_kernel -- this seems even harder
    [DecidableEq E]
    (h : b.iIsOrtho v) :
    Submodule.span K (v '' (Finset.univ.filter fun i => b (v i) (v i) = 0))
    = LinearMap.ker b := by
  simp
  sorry

theorem basis_selforthogonal_iff_in_kernel
    (ortho : b.iIsOrtho v) (symm : b.IsSymm) :
    ∀ i, b (v i) (v i) = 0 ↔ (v i) ∈ (LinearMap.ker b) := by
  intro i
  constructor
  · contrapose!
    intro h
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker b: Submodule K E)
    obtain ⟨w, hw, n, hn, h'⟩ : ∃ w ∈ W, ∃ n ∈ LinearMap.ker b, w + n = v i := by
      rw [← Submodule.mem_sup, hW.symm.sup_eq_top]; exact Submodule.mem_top
    simp at hn
    simp [← h', hn]
    nth_rw 2 [symm.eq]
    simp [hn]

    -- b restricted to the complement of the kernel is nondeg (not true, see below)
    -- by cases: if v i is in the kernel, job done; else b is nondeg on K v i??
    sorry
  · simp
    intro h
    simp [h]



theorem complement_kernel_nondegenerate
    (W : Submodule K E) (h : IsCompl W (LinearMap.ker b))
    (hsymm : LinearMap.IsSymm b) :
    (b.restrict W).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict]
  have h2 := LinearMap.IsSymm.nondegenerate_restrict_of_isCompl_ker hsymm h
  cases h2
  assumption -- ?? how


theorem zero_on_kernel :
    b.restrict (LinearMap.ker b) = 0 := by
  ext x y
  simp only [BilinForm.restrict_apply, LinearMap.map_coe_ker, LinearMap.domRestrict_apply,
    LinearMap.zero_apply]



end FinDim

theorem le_antisymm' (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  omega


example (p : ℕ) (hp : Prime p) : 1 ∣ p := by
  use p
  simp only [one_mul]



/-!
  In this section we show that we can treat kernel of a bilinear map separately
  from the rest of the form.
-/
section SeparateKernel

open Module

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (b : BilinForm K E) (hb : b.IsSymm)
variable {n : Type*} [Fintype n] (v : Basis n K E) (b : BilinForm K E)

lemma ker_imp_nullform
    (hb : b.IsSymm) (ortho : b.iIsOrtho v) :
    ∀ i, b (v i) (v i) = 0 → b (v i) = 0 := by
  intro i hi
  rw [basis_selforthogonal_iff_in_kernel _ _ _] at hi
  assumption'



-- define set of basis vectors that lie in the kernel
variable [DecidablePred fun i : n => b (v i) (v i) = 0]
def A : Finset n :=  Finset.univ.filter (fun i => b (v i) (v i) = 0)

lemma span_A_subset_kernel
    [DecidableEq E]
    (h : b.iIsOrtho v) (symm : b.IsSymm) :
    Submodule.span K ((A v b).image v) ≤ LinearMap.ker b := by
  rw [Submodule.span_le]
  intro w hw
  rcases Finset.mem_image.mp hw with ⟨i, hi, hiw⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  rw [← hiw]
  apply ker_imp_nullform v b symm h
  simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  assumption

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
    apply ker_imp_nullform _ _ hb at hj
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





end SeparateKernel


section SquaringBothSides

open Module

variable {K : Type*} [Field K]
variable {E : Type*} [AddCommGroup E] [Module K E]
variable (b : BilinForm K E) (hb : b.IsSymm)
variable {n : Type*} (v : Basis n K E) (b : BilinForm K E)

theorem squaring_both_sides
    (ortho : b.iIsOrtho v) (A : Set n) [Fintype A] (x : n → K) :
    b (∑ i ∈ A, (x i) • (v i)) (∑ i ∈ A, (x i) • (v i))
      = (∑ i ∈ A, (x i)^2  • (b (v i) (v i)) ) := by
  simp
  have h := LinearMap.BilinForm.iIsOrtho_def.mp ortho
  have inner :
      ∀ i ∈ A.toFinset, (∑ j ∈ A.toFinset, (x j) * (b (v j) (v i))) = (x i) * (b (v i) (v i)) := by
    intro i hi
    apply Finset.sum_eq_single i
    intro k hk hk_ne_i
    have : b (v k) (v i) = 0 := ortho hk_ne_i
    simp [this]
    exact fun a ↦ False.elim (a hi)
  apply Finset.sum_congr rfl
  intro x_1 hx_1
  rwa [inner x_1, ← mul_assoc, pow_two]

end SquaringBothSides


section Sylvester

open Module

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E] [DecidableEq E]
variable (b : BilinForm K E) (hb : b.IsSymm)
variable {n : Type*} [Fintype n] [DecidableEq n]

variable (b1 b2 : Basis n K E)

noncomputable def pS : n → Prop := fun i => b (b1 i) (b1 i) ≥ 0
noncomputable def pT : n → Prop := fun i => b (b2 i) (b2 i) ≤ 0

local notation "pS" => pS b b1
local notation "pT" => pT b b2

noncomputable def S [DecidablePred pS] : Finset n := (Finset.univ : Finset n).filter pS
noncomputable def T := (Finset.univ : Finset n).filter fun i => b (b2 i) (b2 i) ≤ 0

noncomputable def fS [DecidablePred pS] : (S b b1) → E := fun (i : S b b1) => b1 i
noncomputable def fT [DecidablePred pT] : (T b b2) → E := fun (i : T b b2) => b2 i
-- noncomputable def fT := fun i => b2 i

noncomputable def sumST [DecidablePred pS] [DecidablePred pT] :
    (S b b1) ⊕ (T b b2) → E := Sum.elim (fS b b1) (fT b b2)

noncomputable def Basis.isotropic_indices (v : Basis n K E) (b : BilinForm K E) : Finset n :=
  (Finset.univ : Finset n).filter fun i => b (v i) (v i) = 0

noncomputable def Module.Basis.nonisotropic_indices
  (v : Basis n K E) (b : BilinForm K E) : Finset n :=
  (Finset.univ : Finset n).filter fun i => b (v i) (v i) ≠ 0

-- noncomputable def Module.Basis.nonisotropic_vectors
--   (v : Basis n K E) (b : BilinForm K E) : n → E :=
--   nonisotropic_indices v b

local notation "nonIso" => Module.Basis.nonisotropic_indices

theorem foo_same_index
    (b1 b2 : Basis n K E) [DecidablePred pS] [DecidablePred pT] :
  LinearIndependent K (sumST b b1 b2) := by
  sorry

end Sylvester
