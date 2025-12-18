import Mathlib.Data.Real.Basic

/-
  demonstrating quotienting in Lean.
  Lean cleanly avoids setoid hell by axiomatized quotients.

  As a toy example we'll use (a, b) ~ (a + c, b + c) ∀c ∈ ℕ.
  This is equivalent to the proposition
  `(a, b) ~ (a', b') ⇔ a + b' = a' + b`.

  This is isomorphic to ℤ by the maps `[(a, b)] ↦ a - b` and
  `x ↦ [ if x ≥ 0 then (x, 0) else (0, |x|) ]`.
-/


/-
  This does in fact define an equivalence relation.
-/

def int_rel (p q : ℕ × ℕ) : Prop :=
  p.1 + q.2 = q.1 + p.2

lemma int_rel_refl : ∀ p, int_rel p p := by
  intro p
  dsimp [int_rel]

lemma int_rel_symm : ∀ p q, int_rel p q → int_rel q p :=
by
  dsimp [int_rel]
  omega

lemma int_rel_trans : ∀ p q r, int_rel p q → int_rel q r → int_rel p r :=
by
  dsimp [int_rel]
  omega

/-
  We can construct a setoid out of this if we wanted.
-/
instance int_setoid : Setoid (ℕ × ℕ) where
  r := int_rel
  iseqv := ⟨int_rel_refl, @int_rel_symm, @int_rel_trans⟩

/-
  We construct the quotient using Lean's Quot.
-/

def ℤ' : Type := Quot int_setoid

def add_rep (p q : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 + q.1, p.2 + q.2)

-- well-definedness of addition w.r.t. the relation
lemma add_rep_well_defined
  {p p' q q' : ℕ × ℕ}
  (hp : int_rel p p') (hq : int_rel q q') :
  int_rel (add_rep p q) (add_rep p' q') :=
by
  dsimp [int_rel, add_rep] at hp hq ⊢
  omega


/-
  And lift addition on representatives to the quotient type.
-/

def zadd : ℤ' → ℤ' → ℤ' :=
  Quot.lift₂
    (fun p q => Quot.mk int_rel (add_rep p q))
    (by
      intro a b₁ b₂ hb
      apply Quot.sound
      have ha := int_rel_refl a
      exact add_rep_well_defined ha hb)
    (by
      intro a₁ a₂ b ha
      apply Quot.sound
      have hb := int_rel_refl b
      exact add_rep_well_defined ha hb)

instance : Add ℤ' := ⟨zadd⟩

/-
  As an example we show that this operation is commutative.
-/

theorem zadd_comm : ∀ x y : ℤ', x + y = y + x := by
  intro x y
  refine Quot.induction_on₂ x y ?_
  intro p q
  apply Quot.sound
  dsimp [add_rep, int_rel]
  omega

