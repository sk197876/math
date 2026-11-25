(** Local inequalities for the radius limits in Federer (1969), 2.10.19, p.
    181. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PositiveRadiusLimits ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_radius_upper_lt_iff]: supporting local small-ball
    consequence of the strict upper density hypotheses in 2.10.19(1)–(2), p.
    181 *)
Lemma positive_radius_upper_lt_iff (R : realType) (f : R -> \bar R) b :
  positive_radius_upper_limit f<b <->
  exists e : R, (0<e)%R /\ extended_real_sup (positive_radius_values f e)<b.
Proof.
split; last by move=> [e [he hb]]; exact: le_lt_trans (positive_radius_upper_le_level f he) hb.
move=> h; apply: contrapT=> hn.
have hb : b<=positive_radius_upper_limit f.
  apply: extended_real_inf_greatest=> y [e [he ->]].
  rewrite leNgt; apply/negP=> hs; apply: hn; by exists e.
by have := lt_le_trans h hb; rewrite ltxx.
Qed.

(** Source for [positive_radius_upper_large_value]: supporting arbitrarily
    small balls above a strict density threshold in 2.10.19(3), p. 181 *)
Lemma positive_radius_upper_large_value (R : realType) (f : R -> \bar R) b e :
  b<positive_radius_upper_limit f -> (0<e)%R ->
  exists r : R, (0<r<e)%R /\ b<f r.
Proof.
move=> hb he.
have hs := lt_le_trans hb (positive_radius_upper_le_level f he).
apply: contrapT=> hn.
have hle : extended_real_sup (positive_radius_values f e)<=b.
  apply: extended_real_sup_least=> y [r [hr ->]].
  rewrite leNgt; apply/negP=> h; apply: hn; by exists r.
by have := lt_le_trans hs hle; rewrite ltxx.
Qed.

(** Source for [positive_radius_lower_nonnegative]: supporting
    nonnegative lower metric density in 2.10.19,
    p. 181, for a nonnegative measure. *)
Lemma positive_radius_lower_nonnegative (R : realType) (f : R -> \bar R) :
  (forall r : R, (0<r)%R -> 0<=f r) -> 0<=positive_radius_lower_limit f.
Proof.
move=> h; apply: le_trans _ (@positive_radius_lower_ge_level R f 1%R (@ltr01 R)).
apply: extended_real_inf_greatest=> y [r [/andP[hr _] ->]]; exact: h.
Qed.

(** Source for [positive_radius_upper_eventual_bound]: supporting limsup
    bound from a uniform small-radius estimate in 2.10.19, p. 181 *)
Lemma positive_radius_upper_eventual_bound (R : realType) (f : R -> \bar R) b e :
  (0<e)%R -> (forall r : R, (0<r<e)%R -> f r<=b) -> positive_radius_upper_limit f<=b.
Proof.
move=> he h; apply: le_trans (positive_radius_upper_le_level f he) _.
apply: extended_real_sup_least=> y [r [hr ->]]; exact: h.
Qed.
