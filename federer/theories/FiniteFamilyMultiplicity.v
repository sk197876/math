(** Federer (1969), 3.2.39, pp. 275--276: the
    actual number of members of a finite family containing a point. *)
From mathcomp Require Import all_boot boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_family_hit_count]: the cardinality in
    S_j={y:card{C in G:y in f(C)}>=j}, Federer 3.2.39,
    p. 275. This is the actual finite index count; repeated
    set values keep their separate indices, as in a finite
    sum of characteristic functions. *)
Definition finite_family_hit_count (X:Type) (I:finType) (K:I->set X) (y:X):nat:=
  #|[pred i:I|asbool (K i y)]|.

(** Source for [finite_family_hit_count_bound]: the finite
    endpoint v=card G in Federer 3.2.39, p. 275. *)
Lemma finite_family_hit_count_bound (X:Type) (I:finType) (K:I->set X) y:
  (finite_family_hit_count K y<=#|I|)%N.
Proof. exact:max_card. Qed.

(** Source for [finite_family_hit_count_monotone]: supporting
    membership monotonicity for the tube comparison in Federer
    3.2.39, p. 276. It is a count of actual finite indices. *)
Lemma finite_family_hit_count_monotone (X:Type) (I:finType) (K L:I->set X) y:
  (forall i,K i y ->L i y) ->
  (finite_family_hit_count K y<=finite_family_hit_count L y)%N.
Proof.
move=>h.
have hSub:[pred i:I|asbool (K i y)] \subset [pred i:I|asbool (L i y)].
  apply/fintype.subsetP=>i; rewrite !inE=>hi.
  exact (h i hi).
exact:(@subset_leq_card I _ _ hSub).
Qed.

(** Source for [finite_family_hit_count_positive]: S_1 is
    the whole image union in Federer 3.2.39, pp. 275--276. *)
Lemma finite_family_hit_count_positive (X:Type) (I:finType) (K:I->set X) y:
  (0<finite_family_hit_count K y)%N <->(\bigcup_i K i) y.
Proof.
split.
- move/card_gt0P=>[i hi]; exists i; first exact Logic.I.
  by move:hi; rewrite inE.
- move=>[i _ hi]; apply/card_gt0P; exists i; rewrite inE; exact hi.
Qed.

(** Source for [finite_family_hit_count_transport]: the same finite
    indices transfer from a layer centre to a tube point in
    Federer 3.2.39, p. 276. Source and target carriers and
    their tested points may differ. *)
Lemma finite_family_hit_count_transport (X Y:Type) (I:finType) (K:I->set X) (L:I->set Y) x y:
  (forall i,K i x ->L i y) ->
  (finite_family_hit_count K x<=finite_family_hit_count L y)%N.
Proof.
move=>h.
have hSub:[pred i:I|asbool (K i x)] \subset [pred i:I|asbool (L i y)].
  apply/fintype.subsetP=>i; rewrite !inE=>hi.
  exact (h i hi).
exact:(@subset_leq_card I _ _ hSub).
Qed.
