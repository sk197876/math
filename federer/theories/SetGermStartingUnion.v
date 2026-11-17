(** Federer (1969), 3.4.8(11), p. 333:
    after the first irreducible difference is stratified,
    the original S0 and these actual strata represent
    beta union that first irreducible germ. This
    identifies the starting set for the next component. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermExistence SetGermLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_difference_starting_union]:
    the original next excluded germ beta union alpha
    in the successive-difference formula of
    3.4.8(11), p. 333. The original actual
    S0 and stratum union are retained. *)
Theorem set_germ_difference_starting_union (X:topologicalType) a
    (alpha:@set_germ_space X a) (S0 L:set X):
  @SetGerms.meet X a alpha (@SetGerms.neg X a (@set_germ X a S0)) = @set_germ X a L ->
  @set_germ X a (S0 `|` L) = @SetGerms.join X a (@set_germ X a S0) alpha.
Proof.
have [A <-]:=@set_germ_has_representative X a alpha.
rewrite (@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a))
  (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)).
move/set_germ_equality_original=>[U [hU [haU hEqual]]].
rewrite (@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a)).
apply/set_germ_equality_original;exists U;split;first exact:hU.
split;first exact:haU.
apply/seteqP;split.
- move=>x [hUnion hUx];split;last exact:hUx.
  case:hUnion=>[hS0x|hLx];first by left.
  right;have hMember:((A `&` ~` S0) `&` U) x by rewrite hEqual;split.
  exact:hMember.1.1.
- move=>x [hUnion hUx];split;last exact:hUx.
  case:hUnion=>[hS0x|hAx];first by left.
  case:(pselect (S0 x))=>hS0x;first by left.
  right;have hMember:(L `&` U) x by rewrite -hEqual;split;first split.
  exact:hMember.1.
Qed.
