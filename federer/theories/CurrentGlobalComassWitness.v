(** Federer (1969), 4.1.7, p. 358, and
    4.1.19, p. 377: the literal global comass
    records values at individual points.
    These supporting consequences use its original
    supremum laws without replacing it by an
    essential supremum. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations AlternatingForms
  CurrentCoefficientNorms ExtendedSupremumUP
  CurrentGlobalComassUP CurrentGlobalComassSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [current_global_comass_point_lower]:
    M(phi) is the supremum of every pointwise
    comass on U, Federer 4.1.7, p. 358.
    A null exceptional point is still included. *)
Lemma current_global_comass_point_lower
    (R:realType) (h2:((1+1:R)%R!=0%R)) n m
    (U:set (R_n R n))
    (phi:R_n R n->A_m (R_n R n) R^o m) x:
  U x->
  (@current_form_comass R h2 n m (phi x))%:E<=
    @CurrentGlobalComass.value R h2 n m U phi.
Proof.
move=>hx;apply:(extended_supremum_upper
  (@CurrentGlobalComass.laws R h2 n m U phi)).
by exists x.
Qed.

(** Source for [current_global_comass_empty_value]:
    the empty-source endpoint of the original
    global supremum in Federer 4.1.7, p. 358.
    It is minus infinity, whereas a dual
    seminorm on a zero space is zero. *)
Lemma current_global_comass_empty_value
    (R:realType) (h2:((1+1:R)%R!=0%R)) n m
    (phi:R_n R n->A_m (R_n R n) R^o m):
  @CurrentGlobalComass.value R h2 n m set0 phi=-oo.
Proof.
apply/eqP;rewrite eq_le leNye andbT.
apply:(extended_supremum_least
  (@CurrentGlobalComass.laws R h2 n m set0 phi)).
by move=>a [x [[] _]].
Qed.
