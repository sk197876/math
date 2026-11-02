(** Positive-radius limits for Federer (1969), 2.10.19, p. 181, definition
    of upper and lower metric densities as r tends to zero from above.
    Values at zero and at negative radii are excluded. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal lra.
From Federer Require Import ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_radius_values]: supporting range over 0<r<e in the
    one-sided density limits of 2.10.19, p. 181 *)
Definition positive_radius_values (R : realType) (f : R -> \bar R) (e : R) :=
  [set y | exists r : R, (0<r<e)%R /\ y=f r].

(** Source for [positive_radius_upper_limit]: direct limsup
    as r tends to zero from above in 2.10.19,
    p. 181, written with the already sealed extended
    supremum and infimum laws. *)
Definition positive_radius_upper_limit (R : realType) (f : R -> \bar R) :=
  extended_real_inf [set b | exists e : R, (0<e)%R /\ b=extended_real_sup (positive_radius_values f e)].

(** Source for [positive_radius_lower_limit]: direct liminf as r tends to
    zero from above in 2.10.19, p. 181 *)
Definition positive_radius_lower_limit (R : realType) (f : R -> \bar R) :=
  extended_real_sup [set b | exists e : R, (0<e)%R /\ b=extended_real_inf (positive_radius_values f e)].

(** Source for [positive_radius_upper_le_level]: supporting
    upper bound at every positive radius scale for
    2.10.19, p. 181, by the limsup infimum law. *)
Lemma positive_radius_upper_le_level (R : realType) (f : R -> \bar R) e :
  (0<e)%R -> positive_radius_upper_limit f<=extended_real_sup (positive_radius_values f e).
Proof. move=> he; apply: extended_real_inf_lower; by exists e. Qed.

(** Source for [positive_radius_lower_ge_level]: supporting
    lower bound at every positive radius scale for
    2.10.19, p. 181, by the liminf supremum law. *)
Lemma positive_radius_lower_ge_level (R : realType) (f : R -> \bar R) e :
  (0<e)%R -> extended_real_inf (positive_radius_values f e)<=positive_radius_lower_limit f.
Proof. move=> he; apply: extended_real_sup_upper; by exists e. Qed.

(** Source for [positive_radius_limits_ordered]: supporting
    lower density at most upper density in 2.10.19,
    p. 181. Every positive pair of scales has an
    actual common positive radius, so no partial-domain
    or fineness assumption is suppressed. *)
Lemma positive_radius_limits_ordered (R : realType) (f : R -> \bar R) :
  positive_radius_lower_limit f<=positive_radius_upper_limit f.
Proof.
apply: extended_real_sup_least=> b [e [he ->]].
apply: extended_real_inf_greatest=> c [d [hd ->]].
pose r := (Num.min e d/2)%R.
have hr : (0<r)%R by rewrite /r divr_gt0 // lt_min he hd.
have hmin : (0<Num.min e d)%R by rewrite lt_min he hd.
have hhalf : (r<Num.min e d)%R by rewrite /r; lra.
have hme : (Num.min e d<=e)%R by rewrite ge_min lexx.
have hre : (r<e)%R := lt_le_trans hhalf hme.
have hrd : (r<d)%R.
  apply: lt_le_trans hhalf _; by rewrite ge_min lexx orbT.
have hfe : positive_radius_values f e (f r) by exists r; split=> //; by apply/andP.
have hfd : positive_radius_values f d (f r) by exists r; split=> //; by apply/andP.
exact: le_trans (extended_real_inf_lower hfe) (extended_real_sup_upper hfd).
Qed.
