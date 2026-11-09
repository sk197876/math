(** Federer (1969), 3.4.5, pp. 319–321:
    elementary Boolean order laws for original set germs,
    supporting irreducible variety germs and components. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermLaws SetGermOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section BooleanOrder.
Variable X:topologicalType.
Variable a:X.
Local Notation G:=(set_germ_space a).
Local Notation join:=(@SetGerms.join X a).
Local Notation meet:=(@SetGerms.meet X a).
Local Notation germ:=(@set_germ X a).

(** Source for [set_germ_meet_subset_left]: an intersection
    is contained in its first germ, 3.4.5, pp. 320–321. *)
Lemma set_germ_meet_subset_left (alpha beta:G):set_germ_subset (meet alpha beta) alpha.
Proof.
have [S <-]:=@set_germ_has_representative X a alpha.
have [T <-]:=@set_germ_has_representative X a beta.
rewrite (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)).
apply:set_germ_subset_from_sets;by move=>x [hx _].
Qed.

(** Source for [set_germ_meet_subset_right]: an intersection
    is contained in its second germ, 3.4.5, pp. 320–321. *)
Lemma set_germ_meet_subset_right (alpha beta:G):set_germ_subset (meet alpha beta) beta.
Proof. rewrite set_germ_intersection_commutative;exact:set_germ_meet_subset_left. Qed.

(** Source for [set_germ_subset_join_left]: either original
    germ is contained in their union, 3.4.5, pp. 320–321. *)
Lemma set_germ_subset_join_left (alpha beta:G):set_germ_subset alpha (join alpha beta).
Proof.
have [S <-]:=@set_germ_has_representative X a alpha.
have [T <-]:=@set_germ_has_representative X a beta.
rewrite (@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a)).
apply:set_germ_subset_from_sets;by move=>x hx;left.
Qed.

(** Source for [set_germ_subset_join_right]: either original
    germ is contained in their union, 3.4.5, pp. 320–321. *)
Lemma set_germ_subset_join_right (alpha beta:G):set_germ_subset beta (join alpha beta).
Proof. rewrite set_germ_union_commutative;exact:set_germ_subset_join_left. Qed.

(** Source for [set_germ_subset_join_bound]: the original
    union is the least common upper germ, supporting
    components in 3.4.5, p. 321. *)
Lemma set_germ_subset_join_bound (alpha beta gamma:G):
  set_germ_subset alpha gamma ->set_germ_subset beta gamma ->set_germ_subset (join alpha beta) gamma.
Proof.
have [S <-]:=@set_germ_has_representative X a alpha.
have [T <-]:=@set_germ_has_representative X a beta.
have [V <-]:=@set_germ_has_representative X a gamma.
move/set_germ_subset_original=>[U [hU [ha hS]]].
move/set_germ_subset_original=>[W [hW [hb hT]]].
rewrite (@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a)).
apply/set_germ_subset_original;exists (U `&` W);split;first exact:openI hU hW.
split;first by split.
by move=>x [hs|ht] [hu hw];[exact:hS x hs hu|exact:hT x ht hw].
Qed.

(** Source for [set_germ_subset_meet_bound]: the original
    intersection is the greatest common lower germ,
    supporting 3.4.5, pp. 320–321. *)
Lemma set_germ_subset_meet_bound (alpha beta gamma:G):
  set_germ_subset alpha beta ->set_germ_subset alpha gamma ->set_germ_subset alpha (meet beta gamma).
Proof.
rewrite /set_germ_subset=>hAB hAC.
by rewrite set_germ_intersection_associative hAB.
Qed.

(** Source for [set_germ_join_monotone]: inclusion respects
    the induced union, supporting 3.4.5, pp. 320–321. *)
Lemma set_germ_join_monotone (alpha beta gamma delta:G):
  set_germ_subset alpha beta ->set_germ_subset gamma delta ->
  set_germ_subset (join alpha gamma) (join beta delta).
Proof.
move=>hAB hCD;apply:set_germ_subset_join_bound.
- exact:(set_germ_subset_transitive hAB (set_germ_subset_join_left beta delta)).
- exact:(set_germ_subset_transitive hCD (set_germ_subset_join_right beta delta)).
Qed.
End BooleanOrder.
