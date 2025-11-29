import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic

open LinearMap (BilinForm)
open Module
open Classical

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {ι κ : Type*} [Fintype ι]

theorem ortho_reindex
    {b : BilinForm R M} {v : Basis ι R M} (e : ι ≃ κ) (ortho : b.iIsOrtho v) :
    b.iIsOrtho (v.reindex e) := by
  intro i j hij
  have hij' : e.symm i ≠ e.symm j :=
    fun h => hij (by simpa only [Equiv.apply_symm_apply] using congrArg e h)
  have e_ortho := ortho hij'
  rw [Function.onFun_apply] at ⊢ e_ortho
  rwa [Basis.reindex_apply v e i, Basis.reindex_apply v e j]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (b : BilinForm K E)
variable {n : Type*} [Fintype n]
variable (v : Basis n K E) (ortho : b.iIsOrtho v)

variable (v v' : Basis n K E)

def PosP (b : BilinForm K E) (v : Basis n K E) (i : n) : Prop :=
  0 < b (v i) (v i)

def NegP (b : BilinForm K E) (v : Basis n K E) (i : n) : Prop :=
  b (v i) (v i) < 0

lemma nonpos_iff_neg_of_nondeg
    (nondeg : b.Nondegenerate) (ortho : b.iIsOrtho v) :
    ∀ i, ¬ PosP b v i ↔ NegP b v i := by
  simp [PosP]
  intro i
  exact ⟨fun h_le ↦ lt_of_le_of_ne h_le (ortho.not_isOrtho_basis_self_of_nondegenerate nondeg i),
         fun h_lt ↦ le_of_lt h_lt⟩

-- noncomputable def split_type :
--     n ≃ {i // PosP b v i} ⊕ {i // ¬ PosP b v i} := (Equiv.sumCompl (PosP b v)).symm

noncomputable def split_positivity
    (nondeg : b.Nondegenerate) (ortho : b.iIsOrtho v) :
    n ≃ {i // PosP b v i} ⊕ {i // NegP b v i} := by
  let eNeg := (Equiv.subtypeEquivRight (nonpos_iff_neg_of_nondeg b v nondeg ortho)).symm
  let e := (Equiv.sumCompl (PosP b v)).symm
  exact e.trans (Equiv.sumCongr (Equiv.refl _) eNeg.symm)

lemma split_card_of_nondeg_of_ortho
    (nondeg : b.Nondegenerate) (ortho : b.iIsOrtho v) :
    Fintype.card n = (Fintype.card {i // PosP b v i} + Fintype.card {i // NegP b v i}) := by
  rw [Fintype.card_congr (split_positivity b v nondeg ortho)]
  exact Fintype.card_sum

noncomputable def special_map'' :
  {i // PosP b v i} ⊕ {j // NegP b v' j} → E :=
  fun i => Sum.elim (fun ⟨j, _⟩ => v j) (fun ⟨j,_⟩ => v' j) i

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
    exact h_non_s (Sum.inl i) hi_ni_s
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
    exact h_non_s (Sum.inr i) hi_ni_s
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
  have eq_zero_of_le_ge_eq
    {a b : K} (le : 0 ≤ a) (ge : 0 ≥ b) (eq : a = b) :
    a = 0 ∧ b = 0 := by constructor <;> linarith
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

theorem special_set_card_le_finrank
    (v v' : Basis n K E)
    (ortho : b.iIsOrtho v) (ortho' : b.iIsOrtho v') :
    Fintype.card { i // PosP b v i }
      + Fintype.card { j // NegP b v' j }
      ≤ finrank K E := by
    simpa using (special_sum b v v' ortho ortho').fintype_card_le_finrank

theorem special_set_pos_le_pos
    (v v' : Basis n K E) (nondeg : b.Nondegenerate)
    (ortho : b.iIsOrtho v) (ortho' : b.iIsOrtho v') :
    Fintype.card { i // PosP b v i } ≤ Fintype.card { j // PosP b v' j } := by
  have : Fintype.card n - Fintype.card { j // NegP b v' j } = Fintype.card {i // PosP b v' i} := by
    rw [Nat.sub_eq_iff_eq_add ?_] <;> simp [split_card_of_nondeg_of_ortho b v' nondeg ortho']
  rw [← this]
  refine Nat.le_sub_of_add_le ?_
  rw [← finrank_eq_card_basis v]
  exact special_set_card_le_finrank b v v' ortho ortho'

theorem special_set_pos_eq_pos
    (v v' : Basis n K E) (nondeg : b.Nondegenerate)
    (ortho : b.iIsOrtho v) (ortho' : b.iIsOrtho v') :
    Fintype.card { i // PosP b v i } = Fintype.card { j // PosP b v' j } := by
  have := special_set_pos_le_pos b v v' nondeg ortho ortho'
  have := special_set_pos_le_pos b v' v nondeg ortho' ortho
  omega

noncomputable
def Basis.indexEquivFinrank (v : Basis n K E) : n ≃ Fin (finrank K E) := by
  refine Fintype.equivOfCardEq ?_
  simpa [Fintype.card_fin] using (Module.finrank_eq_card_basis v).symm

instance : Invertible (2 : K) where
  invOf := 1/2
  invOf_mul_self := by simp
  mul_invOf_self := by simp

lemma split_card_of_nondeg_of_ortho'
    (nondeg : b.Nondegenerate) (ortho : b.iIsOrtho v) :
    finrank K E = (Fintype.card {i // PosP b v i} + Fintype.card {i // NegP b v i}) := by
  rw [finrank_eq_card_basis v]
  exact split_card_of_nondeg_of_ortho b v nondeg ortho

theorem sylvester
    (nondeg : b.Nondegenerate) (symm : LinearMap.IsSymm b) :
    ∃ r : ℕ, ∀ (v : Basis n K E),
      b.iIsOrtho v →
      Fintype.card { i // PosP (b := b) v i } = r
        ∧
      finrank K E - r = Fintype.card { i // NegP (b := b) v i } := by

  obtain ⟨v₀, hv₀⟩ := LinearMap.BilinForm.exists_orthogonal_basis symm
  refine ⟨Fintype.card { i // PosP b v₀ i }, ?_⟩
  intro v ortho

  let e : n ≃ Fin (finrank K E) := Basis.indexEquivFinrank v
  have pos_equiv : ∀ (a : n), PosP b v a ↔ PosP b (v.reindex e) (e a) := by simp [PosP]
  have posp_reindex_invariant
    : Fintype.card { i // PosP b v i } = Fintype.card { j // PosP b (v.reindex e) j }
    := Fintype.card_congr <| Equiv.subtypeEquiv e pos_equiv

  rw [special_set_pos_eq_pos b v₀ (v.reindex e) nondeg hv₀ (ortho_reindex e ortho)]

  exact ⟨
    posp_reindex_invariant,
    Nat.sub_eq_of_eq_add' <|
      posp_reindex_invariant ▸ split_card_of_nondeg_of_ortho' b v nondeg ortho⟩

