(** Federer (1969), 3.4.5, pp. 319–321:
    whole and empty set-germ boundary cases, needed to
    state irreducibility and proper primeness precisely. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermExistence SetGermLaws SetGermOrder SetGermBooleanOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Boundary.
Variable X:topologicalType.
Variable a:X.
Local Notation G:=(set_germ_space a).
Local Notation germ:=(@set_germ X a).
Local Notation meet:=(@SetGerms.meet X a).
Local Notation join:=(@SetGerms.join X a).

(** Source for [set_germ_intersection_empty]: the empty
    germ absorbs intersections, 3.4.5, pp. 319–320. *)
Lemma set_germ_intersection_empty (alpha:G):meet alpha (germ set0)=germ set0.
Proof.
have [S <-]:=@set_germ_has_representative X a alpha.
by rewrite (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)) setI0.
Qed.

(** Source for [set_germ_empty_subset]: the empty germ
    is contained in every original germ, 3.4.5, pp. 320–321. *)
Lemma set_germ_empty_subset (alpha:G):set_germ_subset (germ set0) alpha.
Proof.
have [S <-]:=@set_germ_has_representative X a alpha.
apply:set_germ_subset_from_sets;by move=>x hx;case:hx.
Qed.

(** Source for [set_germ_subset_empty]: containment in the
    empty germ forces equality to it, 3.4.5, pp. 320–321. *)
Lemma set_germ_subset_empty (alpha:G):set_germ_subset alpha (germ set0) ->alpha=germ set0.
Proof. rewrite /set_germ_subset set_germ_intersection_empty;exact:esym. Qed.

(** Source for [set_germ_empty_not_whole]: the empty
    and whole germs differ at the original centre,
    supporting proper ideals in 3.4.5, p. 320. *)
Lemma set_germ_empty_not_whole:germ set0<>germ setT.
Proof.
move/set_germ_equality_original=>[U [hU [ha hEquality]]].
have hMember:(set0 `&` U) a by rewrite hEquality;split.
exact:hMember.1.
Qed.

(** Source for [set_germ_union_empty_factors]: if a
    union has empty germ then both original germs are
    empty, supporting 3.4.5, pp. 320–321. *)
Lemma set_germ_union_empty_factors (alpha beta:G):
  join alpha beta=germ set0 ->alpha=germ set0 /\beta=germ set0.
Proof.
move=>hUnion;split;apply:set_germ_subset_empty;rewrite -hUnion.
- exact:set_germ_subset_join_left.
- exact:set_germ_subset_join_right.
Qed.
End Boundary.
