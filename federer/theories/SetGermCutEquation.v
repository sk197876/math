(** Federer (1969), 3.4.8(11), pp. 333–334:
    removing the exceptional zero variety from the
    original germ leaves precisely the original
    nonzero equation locus within that variety. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [set_germ_cut_regular_equation]:
    the original regular complement of var(K),
    3.4.8(11), pp. 333–334. The equation
    is an identity of the sealed Boolean operations;
    no analytic or dimensional premise is used. *)
Theorem set_germ_cut_regular_equation (X:topologicalType) (R:zmodType) a (H:set X) (phi:X->R):
  @SetGerms.meet X a (@set_germ X a H)
    (@SetGerms.neg X a (@SetGerms.meet X a (@set_germ X a H)
      (@set_germ X a [set x|phi x=0]))) =
  @set_germ X a [set x|H x /\phi x<>0].
Proof.
rewrite (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a))
  (@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a))
  (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)).
congr (@set_germ X a _);apply/seteqP;split.
- move=>x [hx hNot];split;first exact:hx.
  move=>hZero;apply:hNot;by split.
- move=>x [hx hNonzero];split;first exact:hx.
  by move=>[_ hZero];exact:hNonzero hZero.
Qed.
