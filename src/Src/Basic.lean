import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Basic   -- gives complement on Finset
open LinearMap (BilinForm)
/-!
# Sylvester's Theorem

We're trying to implement sylvester's theorem.
For now, until better ideas strike, we're working against Lang's formulation of the
theorem in terms of symmetric bilinear maps.

-/

/- using selected parts of Lang's chapter XV as exercises -/

section Intro
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
end Intro

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

/-- implements the 'square both sides' argument from Lang's proof. -/
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


/-- attempting Sylvester's theorem (or a critical part of the proof), unsuccessfully.-/
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

instance : DecidablePred pS := inferInstance
instance : DecidablePred pT := inferInstance
noncomputable def S : Finset n := (Finset.univ : Finset n).filter pS
noncomputable def T := (Finset.univ : Finset n).filter fun i => b (b2 i) (b2 i) ≤ 0

noncomputable def fS : (S b b1) → E := fun (i : S b b1) => b1 i
noncomputable def fT : (T b b2) → E := fun (i : T b b2) => b2 i
-- noncomputable def fT := fun i => b2 i

noncomputable def sumST :
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

theorem special_set_linindep
    (b1 b2 : Basis n K E) :
    LinearIndependent K (sumST b b1 b2) := by
  sorry

end Sylvester


section VectorJoin

open Module

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E] [DecidableEq E]
variable (b : BilinForm K E) (hb : b.IsSymm)
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (b1 b2 : Basis n K E)


def joint := {i // b (b1 i) (b1 i) > 0} ⊕ {j // b (b2 j) (b2 j) < 0}
noncomputable def jointf : joint b b1 b2 → E := Sum.elim (fun i => b1 i.1) (fun j => b2 j.1)

lemma sum_sumtype {α β γ : Type} [AddCommMonoid γ]
  [Fintype α] [Fintype β] (f : α ⊕ β → γ) :
  ∑ x : α ⊕ β, f x =
    (∑ a : α, f (Sum.inl a)) + (∑ b : β, f (Sum.inr b)) := by
  rw [Fintype.sum_sum_type]

lemma sum_sumtype_on_subsets {α β γ : Type*} [AddCommMonoid γ]
    [Fintype α] [Fintype β] (f : α ⊕ β → γ) (s : Finset (α ⊕ β)) :
    ∑ x ∈ s, f x =
      ∑ a ∈ s.toLeft, f (Sum.inl a) + ∑ b ∈ s.toRight, f (Sum.inr b) := by
  rw [← Finset.sum_disjSum, Finset.toLeft_disjSum_toRight]


set_option diagnostics true
instance : Fintype (joint b b1 b2) := inferInstance

lemma split_sum_joint (s : Finset (joint b b1 b2)) (coeff : (joint b b1 b2) → K)
    (hzero : ∀i, i ∉ s → coeff i = 0):
    ∑ i ∈ s, (coeff i) • jointf b b1 b2 i
    =
    ∑ a ∈ s.toLeft,
      coeff (Sum.inl a) • b1 a
    +
    ∑ b ∈ s.toRight,
      coeff (Sum.inr b) • b2 b := by
  have s_univ : s ⊆ (Finset.univ) := by simp
  have expanded_sum :
    ∑ i, (coeff i) • jointf b b1 b2 i = ∑ i ∈ s, (coeff i) • jointf b b1 b2 i := by
    rw [Finset.sum_subset s_univ]
    intro x hx hxs
    apply hzero at hxs
    simp [hxs]
  rw [← expanded_sum]
  rw [Fintype.sum_sum_type (fun x => (coeff x) • jointf b b1 b2 x)]
  sorry


theorem joint_linindep :
    LinearIndependent K (jointf b b1 b2) := by
  rw [linearIndependent_iff'']
  intro s coeff h_non_s
  simp [jointf]
  intro hsum_eq
  sorry

end VectorJoin


/- Statements about sums over sum types. 2nd attempt. -/
section SumTypes

/--
  For a sum type, `α ⊕ β`, a sum over it, `∑ i` (i ∈ α ⊕ β), and a subset of it, `s ⊆ α ⊕ β`,
  it should be possible to split the sum along both the type and the set.
  For the type: `∑ i = ∑ a ∈ α + ∑ b ∈ β`.
  For the set:  `∑ i = ∑ i ∈ s + ∑ j ∉ s`.
  And naturally also along both at once.

  The following example is exactly `Fintype.sum_sum_type`. A theorem like `Fintype.sum_sum_set`
  ought to exist. And the immediate consequences `_type_set` and `_set_type` also, and should be
  equal (propositionally).
-/
example {α β γ : Type} [AddCommMonoid γ] [Fintype α] [Fintype β] (f : α ⊕ β → γ) :
  ∑ x : α ⊕ β, f x = (∑ a : α, f (Sum.inl a)) + (∑ b : β, f (Sum.inr b)) := by
  rw [Fintype.sum_sum_type]

variable (ι κ : Type) [Fintype ι] [Fintype κ]
-- def θ := ι ⊕ κ
-- #check θ
-- instance (ι κ) : Fintype (θ ι κ) := inferInstance

abbrev θ := ι ⊕ κ
#check θ
local notation "θ" => θ ι κ
instance : Fintype θ := inferInstance
#check (inferInstance : Fintype θ)

example (s : Finset θ) : Fintype s := by infer_instance

variable {γ : Type*} [AddCommMonoid γ]
-- can't infer instance of HasCompl (Finset θ)
#search "HasCompl for Finsets?"
#check (inferInstance : HasCompl (Finset θ))
#check (inferInstance : HasCompl (Finset ι))

theorem Fintype.sum_sum_subset
    (s : Finset θ) [Fintype s] (f : θ → γ) :
    ∑ i, f i = ∑ i ∈ s, f i + ∑ i ∈ Finset.univ \ s, f i := by
  sorry

variable [DecidableEq ι] [DecidableEq κ] -- this was the culprit
#check (inferInstance : HasCompl (Finset ι))

theorem Fintype.sum_sum_subset'
    (s : Finset θ) (f : θ → γ) :
    ∑ i, f i = ∑ i ∈ s, f i + ∑ i ∉ s, f i := by
  have h : Disjoint s sᶜ := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.inter_compl s
  rw [← Finset.sum_union h, Finset.union_compl]

/- can I split sets along type? -/

variable (t : Finset θ)
#check t.toLeft

/- Why are these not standard? I feel like these could be simpable. -/
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (u : Finset (α ⊕ β))
theorem toLeft_compl : uᶜ.toLeft = u.toLeftᶜ := by ext ; simp
theorem toRight_compl : uᶜ.toRight = u.toRightᶜ := by ext ; simp


theorem Fintype.sum_sum_subset_type
    (s : Finset θ) (f : θ → γ) [CommMonoid γ] :
    ∑ i, f i =
      ∑ i ∈ s.toLeft, f (Sum.inl i) + ∑ i ∉ s.toLeft, f (Sum.inl i)  +
      ∑ i ∈ s.toRight, f (Sum.inr i) + ∑ i ∉ s.toRight, f (Sum.inr i)
  := by
  rw [Fintype.sum_sum_subset' ι κ s,
      Finset.sum_sum_eq_sum_toLeft_add_sum_toRight s f,
      Finset.sum_sum_eq_sum_toLeft_add_sum_toRight sᶜ f]
  abel_nf
  simp [toLeft_compl, toRight_compl]

end SumTypes

section SpecialSet

open Module

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E] [DecidableEq E]
variable (b : BilinForm K E)
variable {n : Type*} [Fintype n] [DecidableEq n]

/-
  Retreatment of the special set that's central to one step of the proof of Lang.

  For a bilinear form `b` and two bases `v`, `v'`, the set
  ```
    s := {i // b vi vi > 0} ⊕ {j // b v'j v'j < 0} ⊆ n ⊕ n
  ```
  is linearly independent.


  Figured out why this set doesn't for for LinearIndependent K s
    s := {i // b (v i) (v i) > 0} ⊕ {j : n // b (v' j) (v' j) < 0}
  because this is a sumtype of _indices_, not vectors. Need to figure out how
  to map them to maps into E.

 -/
variable (v v' : Basis n K E)
abbrev s := {i // b (v i) (v i) > 0} ⊕ {j : n // b (v' j) (v' j) < 0}
#check (s b v v')
def special_map : (s b v v') → E := fun i => Sum.elim v v' i
def special_map' : ( {i // b (v i) (v i) > 0} ⊕ {j : n // b (v' j) (v' j) < 0} ) → E := fun i => Sum.elim v v' i
noncomputable def special_map'' :
  ( {i // b (v i) (v i) > 0} ⊕ {j : n // b (v' j) (v' j) < 0} ) → E :=
  fun i => Sum.elim (fun ⟨j, _⟩ => v j) (fun ⟨j,_⟩ => v' j) i

/- essentially the same as `squaring_both_sides`, but in the form I need below.
   Doesn't work, because the types are ever so slightly different. Doing it
   manually in the middle of the proof. -/
lemma diagonal_sum_of_ortho
    (v : Basis n K E) (ortho : b.iIsOrtho v) (s : Finset n) (coeff coeff' : n → K) :
    ∑ i ∈ s, coeff i * ∑ j ∈ s, coeff' j * b (v j) (v i) =
      ∑ i ∈ s, coeff i * coeff' i * b (v i) (v i) := by
  have inner :
      ∀ i ∈ s, (∑ j ∈ s, (coeff' j) * (b (v j) (v i))) = (coeff' i) * (b (v i) (v i)) := by
    intro i hi
    apply Finset.sum_eq_single i
    intro k hk hk_ne_i
    have : b (v k) (v i) = 0 := ortho hk_ne_i
    simp [this]
    exact fun a ↦ False.elim (a hi)
  apply Finset.sum_congr rfl
  intro i hi
  rwa [inner i, ← mul_assoc]

lemma eq_zero_of_le_ge_eq
    {a b : K} (le : 0 ≤ a) (ge : 0 ≥ b) (eq : a = b) :
    a = 0 ∧ b = 0 := by
  constructor
  · rw [← eq] at ge
    symm
    apply le_antisymm le ge
  · rw [eq] at le
    symm
    apply le_antisymm le ge

theorem special_sum
    (v v' : Basis n K E)
    (ortho : b.iIsOrtho v) (ortho' : b.iIsOrtho v') :
    LinearIndependent K ( special_map'' b v v' ) := by
  rw [linearIndependent_iff'']
  intro s coeff h_non_s
  simp only [special_map'']
  intro hsum_eq
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight s _] at hsum_eq
  simp at hsum_eq
  rw [add_eq_zero_iff_eq_neg] at hsum_eq
  have h := congr_arg (fun w => b w w) hsum_eq
  simp only [map_sum, map_smul, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, map_neg, LinearMap.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg] at h
  have inner :
    ∀ i ∈ s.toLeft,
      (∑ j ∈ s.toLeft, (coeff (Sum.inl j)) * (b (v j) (v i))) =
      (coeff (Sum.inl i)) * (b (v i) (v i)) := by
    intro i his
    apply Finset.sum_eq_single i
    intro k hk hk_ne_i
    have : b (v k) (v i) = 0 := ortho (Subtype.coe_ne_coe.mpr hk_ne_i)
    simp [this]
    simp
    intro hi_ni_s
    left
    apply h_non_s
    assumption
  have outer :
    ∑ x ∈ s.toLeft, coeff (Sum.inl x) * ∑ x_1 ∈ s.toLeft, coeff (Sum.inl x_1) * (b (v ↑x_1)) (v ↑x)
      = ∑ x ∈ s.toLeft, coeff (Sum.inl x) * coeff (Sum.inl x) * (b (v ↑x)) (v ↑x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rwa [inner x, ← mul_assoc]
  rw [outer] at h
  have inner :
    ∀ i ∈ s.toRight,
      (∑ j ∈ s.toRight, (coeff (Sum.inr j)) * (b (v' j) (v' i))) =
      (coeff (Sum.inr i)) * (b (v' i) (v' i)) := by
    intro i his
    apply Finset.sum_eq_single i
    intro k hk hk_ne_i
    have : b (v' k) (v' i) = 0 := ortho' (Subtype.coe_ne_coe.mpr hk_ne_i)
    simp [this]
    simp
    intro hi_ni_s
    left
    apply h_non_s
    assumption
  have outer :
    ∑ x ∈ s.toRight, coeff (Sum.inr x)
      * ∑ x_1 ∈ s.toRight, coeff (Sum.inr x_1) * (b (v' ↑x_1)) (v' ↑x)
      = ∑ x ∈ s.toRight, coeff (Sum.inr x) * coeff (Sum.inr x) * (b (v' ↑x)) (v' ↑x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rwa [inner x, ← mul_assoc]
  rw [outer] at h
  have left_ge_zero :
    ∑ x ∈ s.toLeft, coeff (Sum.inl x) * coeff (Sum.inl x) * (b (v ↑x)) (v ↑x) ≥ 0 := by
    apply Finset.sum_nonneg
    intro i hi
    rw [mul_comm]
    apply mul_nonneg
    · simpa using le_of_lt (Subtype.prop i)
    · rw [← pow_two]
      apply sq_nonneg
  have right_le_zero :
    ∑ x ∈ s.toRight, coeff (Sum.inr x) * coeff (Sum.inr x) * (b (v' ↑x)) (v' ↑x) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    rw [mul_comm]
    apply mul_nonpos_iff.mpr
    right
    constructor
    · exact le_of_lt (Subtype.prop i)
    · rw [← pow_two]
      apply sq_nonneg
  have ⟨v_eq, v'_eq⟩ := eq_zero_of_le_ge_eq left_ge_zero right_le_zero h
  have v_summand_zero :
    ∀ x ∈ s.toLeft, coeff (Sum.inl x) * coeff (Sum.inl x) * (b (v ↑x)) (v ↑x) ≥ 0 := by
    intro x hx
    apply mul_nonneg
    · rw [← pow_two]
      exact sq_nonneg (coeff (Sum.inl x))
    · exact le_of_lt (Subtype.prop x)
  rw [Finset.sum_eq_zero_iff_of_nonneg v_summand_zero] at v_eq
  have v'_summand_zero :
    ∀ x ∈ s.toRight, coeff (Sum.inr x) * coeff (Sum.inr x) * (b (v' ↑x)) (v' ↑x) ≤ 0 := by
    intro x hx
    apply mul_nonpos_iff.mpr
    left
    constructor
    · rw [← pow_two]
      exact sq_nonneg (coeff (Sum.inr x))
    · exact le_of_lt (Subtype.prop x)
  rw [Finset.sum_eq_zero_iff_of_nonpos v'_summand_zero] at v'_eq
  intro i
  by_cases hi : i ∈ s
  · rcases i with i | j
    · specialize v_eq i (Finset.mem_toLeft.mpr hi)
      have : 0 < (b (v ↑i)) (v ↑i) := by
        exact (Subtype.prop i)
      apply eq_zero_of_ne_zero_of_mul_right_eq_zero (ne_of_gt this) at v_eq
      apply eq_zero_of_mul_self_eq_zero at v_eq
      assumption
    · specialize v'_eq j (Finset.mem_toRight.mpr hi)
      have : (b (v' ↑j)) (v' ↑j) < 0 := by
        exact (Subtype.prop j)
      apply eq_zero_of_ne_zero_of_mul_right_eq_zero (ne_of_lt this) at v'_eq
      apply eq_zero_of_mul_self_eq_zero at v'_eq
      assumption
  · exact h_non_s i hi

end SpecialSet

