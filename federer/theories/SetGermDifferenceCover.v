(** Federer (1969), corrected 3.4.8(11), pp. 327, 333–335:
    the earlier strata representing gamma minus beta,
    together with the original S0 representing beta,
    cover an actual representative of gamma near zero.
    This supplies the published earlier-boundary condition. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermExistence SetGermLaws SetGermOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_difference_local_cover]:
    choose the final neighbourhood so that its
    exceptional variety lies in S0 and earlier
    strata, published correction at book p. 327
    line 24, used in the proof on pp. 333–335. *)
Theorem set_germ_difference_local_cover (X:topologicalType) (a:X) (G S0 L:set X):
  @SetGerms.meet X a (@set_germ X a G) (@SetGerms.neg X a (@set_germ X a S0)) =
    @set_germ X a L ->
  exists W:set X,open W /\W a /\forall x,G x ->W x ->(S0 `|` L) x.
Proof.
move=>hDifference.
rewrite (@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a))
  (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)) in hDifference.
have [W [hW [haW hEqual]]]:=(@set_germ_equality_original X a (G `&` ~` S0) L).1 hDifference.
exists W;split;first exact:hW.
split;first exact:haW.
move=>x hGx hWx;case:(pselect (S0 x))=>hS0x;first by left.
right;have hMember:(L `&` W) x by rewrite -hEqual;split;first split.
exact:hMember.1.
Qed.
