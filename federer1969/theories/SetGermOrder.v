(** Federer (1969), 3.4.5, pp. 320–321:
    inclusion of set germs is the induced Boolean order.
    Its exact local-inclusion criterion uses actual open
    neighbourhoods of the original centre. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermExistence SetGermLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_subset]: containment of germs
    in the variety and component assertions of 3.4.5,
    pp. 320–321, specified by their Boolean intersection. *)
Definition set_germ_subset (X:topologicalType) (a:X) (alpha beta:set_germ_space a):=
  @SetGerms.meet X a alpha beta=alpha.

(** Source for [set_germ_subset_original]: containment of
    germs means containment of original sets on some actual
    neighbourhood, 3.4.5, pp. 320–321. *)
Lemma set_germ_subset_original (X:topologicalType) (a:X) (S T:set X):
  set_germ_subset (set_germ a S) (set_germ a T) <->
  exists U:set X,open U /\U a /\forall x,S x ->U x ->T x.
Proof.
rewrite /set_germ_subset (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a))
  set_germ_equality_original;split.
- move=>[U [hU [ha hEq]]];exists U;split;first exact:hU.
  split;first exact:ha.
  move=>x hx hu;have hMember:((S `&` T) `&` U) x by rewrite hEq;split.
  exact:hMember.1.2.
- move=>[U [hU [ha hSub]]];exists U;split;first exact:hU.
  split;first exact:ha.
  apply/seteqP;split.
  + by move=>x [[hs ht] hu];split.
  + move=>x [hs hu];split;last exact:hu.
    split;[exact:hs|exact:hSub x hs hu].
Qed.

(** Source for [set_germ_subset_from_sets]: ordinary set
    containment implies germ containment, as used throughout
    3.4.5, pp. 320–321. *)
Lemma set_germ_subset_from_sets (X:topologicalType) (a:X) (S T:set X):
  S `<=` T ->set_germ_subset (set_germ a S) (set_germ a T).
Proof.
move=>hSub;apply/set_germ_subset_original;exists setT;split;first exact:openT.
split;first exact:Logic.I.
by move=>x hx _;exact:hSub x hx.
Qed.

(** Source for [set_germ_subset_reflexive]: containment is
    reflexive, supporting the variety order in 3.4.5, p. 321. *)
Lemma set_germ_subset_reflexive (X:topologicalType) (a:X) (alpha:set_germ_space a):
  set_germ_subset alpha alpha.
Proof.
have [S <-]:=@set_germ_has_representative X a alpha.
apply:set_germ_subset_from_sets;by move=>x hx.
Qed.

(** Source for [set_germ_subset_transitive]: local containment
    is transitive, 3.4.5, pp. 320–321. *)
Lemma set_germ_subset_transitive (X:topologicalType) (a:X) (alpha beta gamma:set_germ_space a):
  set_germ_subset alpha beta ->set_germ_subset beta gamma ->set_germ_subset alpha gamma.
Proof.
have [S <-]:=@set_germ_has_representative X a alpha.
have [T <-]:=@set_germ_has_representative X a beta.
have [V <-]:=@set_germ_has_representative X a gamma.
move/set_germ_subset_original=>[U [hU [ha hST]]].
move/set_germ_subset_original=>[W [hW [hb hTV]]].
apply/set_germ_subset_original;exists (U `&` W);split;first exact:openI hU hW.
split;first by split.
move=>x hx [hu hw];exact:hTV x (hST x hx hu) hw.
Qed.

(** Source for [set_germ_subset_antisymmetric]: mutual local
    containment is equality of germs, 3.4.5, pp. 320–321. *)
Lemma set_germ_subset_antisymmetric (X:topologicalType) (a:X) (alpha beta:set_germ_space a):
  set_germ_subset alpha beta ->set_germ_subset beta alpha ->alpha=beta.
Proof.
rewrite /set_germ_subset=>hAB hBA.
by rewrite -hAB set_germ_intersection_commutative hBA.
Qed.
