import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Data.Real.Basic

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
variable (g : LinearMap.BilinForm ℝ V)


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
variable (n : LinearMap.BilinForm K V)
variable (hb : n.IsSymm)

def nullform : Prop := ∀x y : V, n x y = 0

example:
    (∀ z : V, n z z = 0) → nullform n := by
  intros H
  unfold nullform
  intros x y
  have Hsum := H (x+y)
  have Hdiff := H (x-y)
  have H4xy := congrArg₂ (. - .) Hsum Hdiff
  simp at *
  have Hxx0 := H x
  have Hyy0 := H y
  rw [Hxx0, Hyy0] at H4xy
  simp [sub_eq_add_neg] at H4xy
  rw [hb.eq y x] at H4xy
  abel_nf at H4xy
  have Hchar_not_2 : NeZero (2 : K) := inferInstance
  simp at H4xy
  rcases H4xy with ha | hb
  sorry
  exact hb



end Nullform

-- variable {E : Type*} [AddCommMonoid E] [Module ℝ E]



-- theorem sylvester (B: LinearMap.BilinForm ℝ E) (nonDeg: LinearMap.BilinForm.Nondegenerate B) :
--   ∃ r ∈ ℕ, |positive v| = r := by
--   sorry
