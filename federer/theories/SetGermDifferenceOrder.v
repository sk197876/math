(** Federer (1969), 3.4.8(10), p. 331:
    split the original set germ along the
    zero set of delta. Use only the
    sealed Boolean laws of 3.4.5, pp. 319–320. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermLaws SetGermOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section DifferenceOrder.
Variable X:topologicalType.
Variable a:X.
Local Notation G:=(set_germ_space a).
Local Notation meet:=(@SetGerms.meet X a).
Local Notation join:=(@SetGerms.join X a).
Local Notation neg:=(@SetGerms.neg X a).

(** Source for [set_germ_difference_union_cancel]:
    outside delta's zero germ, containment in
    its union with another germ gives containment
    in that other germ, 3.4.8(10), p. 331. *)
Lemma set_germ_difference_union_cancel (alpha beta delta:G):
  set_germ_subset alpha (join delta beta) ->
  set_germ_subset (meet alpha (neg delta)) beta.
Proof.
have [A <-]:=@set_germ_has_representative X a alpha.
have [B <-]:=@set_germ_has_representative X a beta.
have [D <-]:=@set_germ_has_representative X a delta.
rewrite (@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a))
  (@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a))
  (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a))
  !set_germ_subset_original.
move=>[U [hU [ha hSubset]]];exists U;split;first exact:hU.
split;first exact:ha.
move=>x [hA hNot] hUX;case:(hSubset x hA hUX)=>[hD|hB];last exact:hB.
by exfalso;exact:hNot hD.
Qed.

(** Source for [set_germ_split_equation]:
    a germ is the union of its
    parts on and off delta's zero germ,
    3.4.8(10), p. 331. *)
Lemma set_germ_split_equation (alpha delta:G):
  alpha = join (meet alpha delta) (meet alpha (neg delta)).
Proof.
have [A <-]:=@set_germ_has_representative X a alpha.
have [D <-]:=@set_germ_has_representative X a delta.
rewrite (@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a))
  !(@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a))
  (@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a)).
congr (@set_germ X a _);apply/seteqP;split.
- move=>x hA;case:(pselect (D x))=>hD;[left|right];by split.
- by move=>x [[hA _]|[hA _]].
Qed.
End DifferenceOrder.
