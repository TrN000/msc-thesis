import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
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

#check LinearOrderedField -- should I use this? it's how it's done in Lang, but usually ℝ is used.

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
  by_contra
  · have h4 : (4 : K) ≠ 0 := by convert mul_ne_zero H2.ne H2.ne ; norm_num
    contradiction
  · exact hb



end Nullform


section FinDim


-- field with characteristic ≠ 0
variable {k : Type*} [Field k] [NeZero (2 : k)]
-- vsp over this field
variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]


-- Ordered field
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [NeZero (2 : K)]
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

universe w
open Module

theorem square_obasis_nonzero
    {n : Type w} {v : Basis n K E} (h : b.iIsOrtho v) (hb : b.Nondegenerate) :
    ∀ i, b (v i) (v i) ≠ 0 := by
  intro i
  have ho : ¬b.IsOrtho (v i) (v i) := by
    apply h.not_isOrtho_basis_self_of_nondegenerate
    assumption
  rw [b.isOrtho_def] at ho
  assumption

theorem square_obasis_ltzero_or_gtzero
    {n : Type w} {v : Basis n K E} (h : b.iIsOrtho v) (hb : b.Nondegenerate) :
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

theorem basis_selforthogonal_iff_in_kernel :
    ∀ i, b (v i) (v i) = 0 ↔ (v i) ∈ (LinearMap.ker b) := by
  intro i
  constructor
  · simp
    intro h
    -- b restricted to the complement of the kernel is nondeg (not true, see below)
    -- by cases: if v i is in the kernel, job done; else b is nondeg on K v i??
    sorry
  · simp
    intro h
    simp [h]



theorem complement_kernel_nondegenerate :
    (b.restrict (b.orthogonal (LinearMap.ker b))).Nondegenerate := by
  intro v
  simp
  intro h
  -- I don't think this works. Is the kernel in its own orth complement?
  -- It's certainly true on E/ker(b), but this doesn't hold
  sorry


theorem zero_on_kernel :
    b.restrict (LinearMap.ker b) = 0 := by
  ext x y
  simp




end FinDim

theorem le_antisymm' (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  omega


example (p : ℕ) (hp : Prime p) : 1 ∣ p := by
  use p
  simp



-- variable {E : Type*} [AddCommMonoid E] [Module ℝ E]



-- theorem sylvester (B: LinearMap.BilinForm ℝ E) (nonDeg: LinearMap.BilinForm.Nondegenerate B) :
--   ∃ r ∈ ℕ, |positive v| = r := by
--   sorry
