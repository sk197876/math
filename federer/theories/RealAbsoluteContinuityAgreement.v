(** Supporting localisation in Federer (1969), 2.9.21, p. 166: absolute
    continuity on [a,b] depends only on values there. This follows directly
    from the finite-family law in 2.9.20(3), p. 165. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import OrderedIntervalFamilyUP RealAbsoluteContinuityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [ordered_interval_increment_sum_agree]: supporting locality
    of condition (3) of Federer 2.9.20, p. 165, used in 2.9.21, p. 166
    Curves agreeing on the ambient segment have equal increment sums on
    every eligible family. *)
Lemma ordered_interval_increment_sum_agree (R : realType) (g h : R -> R)
    (a b : R) (s : seq (R * R)) :
  (forall x, a<=x -> x<=b -> g x=h x) ->
  is_ordered_real_interval_family a b s ->
  real_interval_family_increment_sum g s=real_interval_family_increment_sum h s.
Proof.
move=> he hs; rewrite /real_interval_family_increment_sum !big_seq.
apply: eq_bigr=> uv huv; case: uv huv=> u v huv.
have [hau [huv' hvb]] := ordered_real_interval_family_cell_bounds hs huv.
by rewrite (he u hau (le_trans (ltW huv') hvb))
  (he v (le_trans hau (ltW huv')) hvb).
Qed.

(** Source for [real_absolute_continuity_agree]: supporting localisation of
    absolute continuity in Federer 2.9.21, p. 166, directly from 2.9.20(3),
    p. 165 Values outside [a,b] impose no condition on absolute continuity
    on that segment. *)
Lemma real_absolute_continuity_agree (R : realType) (g h : R -> R) (a b : R) :
  (forall x, a<=x -> x<=b -> g x=h x) ->
  (is_absolutely_continuous_real_curve g a b <-> is_absolutely_continuous_real_curve h a b).
Proof.
move=> he; split=> hAC e hepos; have [d [hd hbound]] := hAC e hepos;
  exists d; split=> // s hs hlen.
- rewrite -(ordered_interval_increment_sum_agree he hs); exact: hbound s hs hlen.
- rewrite (ordered_interval_increment_sum_agree he hs); exact: hbound s hs hlen.
Qed.
