(** Federer (1969), 3.4.8(11), pp. 333–334:
    split the original variety difference into the
    exceptional difference and the final regular part.
    Only the sealed Boolean laws and actual
    local containment of germs are needed. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermExistence SetGermLaws
  SetGermOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section CutDifference.
Variable X:topologicalType.
Variable a:X.
Local Notation G:=(set_germ_space a).
Local Notation join:=(@SetGerms.join X a).
Local Notation meet:=(@SetGerms.meet X a).
Local Notation neg:=(@SetGerms.neg X a).
Local Notation germ:=(@set_germ X a).

(** Source for [set_germ_cut_difference_split]:
    the exact displayed variety-difference decomposition
    in 3.4.8(11), pp. 333–334.
    The exceptional germ lies in alpha and
    contains alpha intersect beta; beta itself
    need not be contained in alpha. *)
Lemma set_germ_cut_difference_split (alpha beta gamma:G):
  set_germ_subset gamma alpha ->set_germ_subset (meet alpha beta) gamma ->
  meet alpha (neg beta) = join (meet gamma (neg beta)) (meet alpha (neg gamma)).
Proof.
have [A <-]:=@set_germ_has_representative X a alpha.
have [B <-]:=@set_germ_has_representative X a beta.
have [C <-]:=@set_germ_has_representative X a gamma.
move=>hCA hABC.
have [U [hU [haU hCAU]]]:=(@set_germ_subset_original X a C A).1 hCA.
rewrite (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)) in hABC.
have [V [hV [haV hABCV]]]:=(@set_germ_subset_original X a (A `&` B) C).1 hABC.
rewrite !(@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a))
  !(@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a))
  !(@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a)).
apply/set_germ_equality_original;exists (U `&` V);split;first exact:openI hU hV.
split;first by split.
apply/seteqP;split.
- move=>x [[hAx hNotB] [hUx hVx]];split;last by split.
  case:(pselect (C x))=>hCx.
  + left;by split.
  + right;by split.
- move=>x [hUnion [hUx hVx]];split;last by split.
  case:hUnion=>[[hCx hNotB]|[hAx hNotC]].
  + split;first exact:hCAU x hCx hUx.
    exact:hNotB.
  + split;first exact:hAx.
    move=>hBx;apply:hNotC;apply:hABCV;[by split|exact:hVx].
Qed.
End CutDifference.
