(** Supporting the Borel generation argument needed for the section-volume
    refinement of Federer (1969), 2.10.46, p. 204. This auxiliary family
    specification isolates whole-set membership, nested differences and
    disjoint sequence unions from the Borel laws of 2.2.1, pp. 59–60. It
    introduces no project axiom. The pi-lambda proof is an additional proof
    route, not a theorem attributed verbatim to Federer. *)
From mathcomp Require Import all_boot boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_dynkin_family]: auxiliary closure
    specification supporting 2.10.46, p. 204, derived
    from the set-family operations of 2.2.1, pp. 59–60. *)
Record is_dynkin_family (X : Type) (F : set (set X)) : Prop := {
  (** Source for [dynkin_family_whole]: whole-set closure
      used in the supporting Borel generation argument for
      2.10.46, p. 204, from the operations in
      2.2.1, pp. 59–60. *)
  dynkin_family_whole : F setT;
  (** Source for [dynkin_family_nested_difference]: nested
      difference closure used in that argument for 2.10.46,
      p. 204, from 2.2.1, pp. 59–60. *)
  dynkin_family_nested_difference : forall A B, F A -> F B -> A `<=` B -> F (B `\` A);
  (** Source for [dynkin_family_disjoint_union]: disjoint
      sequence-union closure, the operation in 2.2.1(2)', p. 60. *)
  dynkin_family_disjoint_union : forall A : nat -> set X,
    (forall n, F (A n)) ->
    (forall n m, n != m -> forall x, A n x -> A m x -> False) -> F (\bigcup_n A n)
}.

(** Source for [dynkin_family_empty]: supporting empty-set
    consequence of the family laws used for 2.10.46,
    p. 204; subtract the whole set from itself. *)
Lemma dynkin_family_empty (X : Type) (F : set (set X)) : is_dynkin_family F -> F set0.
Proof.
move=> hF; have h := dynkin_family_nested_difference hF
  (dynkin_family_whole hF) (dynkin_family_whole hF) (@subset_refl X setT).
by rewrite setDv in h.
Qed.

(** Source for [dynkin_family_complement]: supporting
    complement consequence of the same family laws for
    2.10.46, p. 204, from 2.2.1, pp. 59–60. *)
Lemma dynkin_family_complement (X : Type) (F : set (set X)) :
  is_dynkin_family F -> forall A, F A -> F (~` A).
Proof.
move=> hF A hA; have h := dynkin_family_nested_difference hF hA (dynkin_family_whole hF) (subsetT A).
by rewrite setTD in h.
Qed.

(** Source for [dynkin_intersection_test_family]: supporting
    fixed-intersection family in the pi-lambda argument for
    2.10.46, p. 204. Its whole-set law uses F A;
    nested differences and disjoint unions distribute over A. *)
Lemma dynkin_intersection_test_family (X : Type) (F : set (set X)) (A : set X) :
  is_dynkin_family F -> F A -> is_dynkin_family [set B | F B /\ F (A `&` B)].
Proof.
move=> hF hA; constructor.
- split; first exact: dynkin_family_whole hF.
  by rewrite setIT.
- move=> B C [hB hAB] [hC hAC] hBC; split.
  + exact (@dynkin_family_nested_difference X F hF B C hB hC hBC).
  + have hi : A `&` B `<=` A `&` C by move=> x [ha hb]; split=> //; exact: hBC.
    have h := dynkin_family_nested_difference hF hAB hAC hi.
    have he : A `&` (C `\` B)=(A `&` C) `\` (A `&` B).
      apply/seteqP; split=> [x [ha [hc hn]]|x [[ha hc] hn]].
      * split; first by split.
        by move=> [_ hb]; exact: hn hb.
      * split=> //; split=> // hb; apply: hn; by split.
    by rewrite he.
- move=> B hB hd; split.
  + apply: (dynkin_family_disjoint_union hF) hd=> n; exact: (hB n).1.
  + have hdis n m : n != m -> forall x, (A `&` B n) x -> (A `&` B m) x -> False.
      move=> hne x [_ hn] [_ hm]; exact: hd n m hne x hn hm.
    have h := dynkin_family_disjoint_union hF (fun n=>(hB n).2) hdis.
    have he : A `&` (\bigcup_n B n)=\bigcup_n (A `&` B n).
      apply/seteqP; split=> [x [ha [n _ hb]]|x [n _ [ha hb]]].
      * exists n=> //; by split.
      * split=> //; by exists n.
    by rewrite he.
Qed.
