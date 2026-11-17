(** Federer (1969), 3.4.8(11), p. 333:
    reduce a finite union of irreducible
    germs to successive differences, excluding beta
    and every earlier member. These supporting
    identities use only the sealed Boolean laws. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermLaws SetGermFiniteUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Differences.
Variable X:topologicalType.
Variable a:X.
Local Notation G:=(set_germ_space a).
Local Notation join:=(@SetGerms.join X a).
Local Notation meet:=(@SetGerms.meet X a).
Local Notation neg:=(@SetGerms.neg X a).
Local Notation union:=(@set_germ_finite_union X a).

(** Source for [set_germ_union_ordered_difference]:
    split a union minus beta into
    the first difference and the remaining
    difference avoiding the first germ,
    3.4.8(11), p. 333. *)
Lemma set_germ_union_ordered_difference (alpha gamma beta:G):
  meet (join alpha gamma) (neg beta) =
  join (meet alpha (neg beta)) (meet gamma (neg (join beta alpha))).
Proof.
have [A <-]:=@set_germ_has_representative X a alpha.
have [C <-]:=@set_germ_has_representative X a gamma.
have [B <-]:=@set_germ_has_representative X a beta.
rewrite !(@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a))
  !(@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a))
  !(@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a))
  !(@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a)).
congr (@set_germ X a _);apply/seteqP;split.
- move=>x [[hA|hC] hNotB];first by left;split.
  case:(pselect (A x))=>hA;first by left;split.
  right;split;first exact:hC.
  by move=>[hB|hAx];[exact:hNotB hB|exact:hA hAx].
- move=>x [[hA hNotB]|[hC hNot]];split.
  + by left.
  + exact:hNotB.
  + by right.
  + by move=>hB;apply:hNot;left.
Qed.

(** Source for [ordered_set_germ_differences]:
    the finite list of successive differences
    in the displayed irreducible-component reduction,
    3.4.8(11), p. 333. This finite
    Boolean operation selects no representative. *)
Fixpoint ordered_set_germ_differences (beta:G) (F:seq G):seq G:=
  if F is alpha::rest then
    meet alpha (neg beta)::ordered_set_germ_differences (join beta alpha) rest
  else [::].

(** Source for [set_germ_finite_union_ordered_differences]:
    the exact finite-union difference identity
    displayed in 3.4.8(11), p. 333. *)
Lemma set_germ_finite_union_ordered_differences (F:seq G) (beta:G):
  meet (union F) (neg beta) = union (ordered_set_germ_differences beta F).
Proof.
elim:F beta=>[|alpha F ih] beta /=.
- have [B <-]:=@set_germ_has_representative X a beta.
  rewrite (@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a))
    (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)) set0I.
  reflexivity.
- by rewrite set_germ_union_ordered_difference ih.
Qed.
End Differences.
