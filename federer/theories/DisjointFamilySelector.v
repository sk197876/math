(** Federer (1969), 2.2.1, p. 60: supporting selection
    of the unique partition member containing a point. Existence
    follows from set theory after disjointness is proved; no member
    of an empty family is postulated. Used in 3.2.48, p. 285. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import CountablyClosedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_disjoint_family_selector]: independent supporting
    laws for the unique piece of a partition, 2.2.1, p. 60,
    used to keep orbit labels invariant in 3.2.48, p. 285.
    Only points in an actual partition member impose a value. *)
Definition is_disjoint_family_selector (X:Type) (P:set (set X)) (s:X->set X):=
  forall B,P B ->forall x,B x ->s x=B.

(** Source for [disjoint_family_selector_exists]: existence for the
    preceding independent laws, supporting the partition reduction
    in 3.2.48, p. 285. The off-union value is irrelevant;
    uniqueness on the union is proved from actual disjointness. *)
Lemma disjoint_family_selector_exists (X:choiceType) (P:set (set X)):
  set_family_disjoint P ->exists s,is_disjoint_family_selector P s.
Proof.
move=>hDisjoint.
have hPoint x:exists B,forall C,P C ->C x ->B=C.
  have [[B [hB hx]]|hNone]:=pselect (exists B,P B /\B x).
  - exists B; move=>C hC hxC.
    have [hEq|hNe]:=pselect (B=C); first exact hEq.
    exfalso; have hEmpty:=hDisjoint B C hB hC hNe.
    have hBoth:(B `&` C) x by split.
    by rewrite hEmpty in hBoth.
  - exists set0; move=>C hC hx; exfalso; apply hNone; by exists C.
have [s hS]:=choice hPoint.
exists s; move=>B hB x hx; exact (hS x B hB hx).
Qed.
