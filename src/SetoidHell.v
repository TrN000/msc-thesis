Require Import Coq.Arith.Arith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Lia.

(* Demonstration of setoid hell in Rocq.

  As with the lean example, we begin by showing that the relation
 `int_rel` is in fact an equivalence relation. *)

Definition int_rel (p q : nat * nat) : Prop :=
  fst p + snd q = fst q + snd p.

Lemma int_rel_refl : forall p, int_rel p p.
Proof.
  intro p. unfold int_rel. reflexivity.
Qed.

Lemma int_rel_sym :
  forall p q, int_rel p q -> int_rel q p.
Proof.
  intros p q H. unfold int_rel in *. symmetry. assumption.
Qed.

Lemma int_rel_trans : forall p q r,
  int_rel p q -> int_rel q r -> int_rel p r.
Proof.
  intros p q r Hpq Hqr.
  unfold int_rel in *.
  lia.
Qed.

Instance int_rel_equiv : Equivalence int_rel :=
  { Equivalence_Reflexive  := int_rel_refl
  ; Equivalence_Symmetric  := int_rel_sym
  ; Equivalence_Transitive := int_rel_trans }.

Add Relation (nat * nat) int_rel
  reflexivity proved by int_rel_refl
  symmetry proved by int_rel_sym
  transitivity proved by int_rel_trans
  as int_rel_setoid.

Definition add_pair (p q : nat * nat) : nat * nat :=
  (fst p + fst q, snd p + snd q).

(* To be able to rewrite modulo int_rel,
   Coq wants a Proper instance: *)
Global Instance add_pair_Proper :
  Proper (int_rel ==> int_rel ==> int_rel) add_pair.
Proof.
  intros p p' Hp q q' Hq.
  unfold add_pair, int_rel in *.
  simpl.
  lia.
Qed.

(* Example where this morphism shows up.
   We prove that this addition commutes. *)

Lemma add_pair_comm : forall p q, int_rel (add_pair p q) (add_pair q p).
Proof.
  intros p q.
  unfold add_pair, int_rel; cbn; lia.
Qed.

Lemma add_pair_comm_respects :
  forall p p' q q',
    int_rel p p' ->
    int_rel q q' ->
    int_rel (add_pair p q) (add_pair q' p').
Proof.
  intros p p' q q' Hp Hq.
  (* Note use of `setoid_rewrite`. *)
  setoid_rewrite Hp.
  setoid_rewrite Hq.
  apply add_pair_comm.
Qed.

