(** Federer (1969), 2.3.8, p. 78, second display: the infimum threshold
    itself satisfies the measure bound, using increasing continuity from
    2.1.3(4). Source context and partial-domain convention: MeasureGauge.v.
    Only measurability of the norm superlevels is needed here; the
    normed-space application supplies it later. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic
  MeasureContinuityBelow ExtendedRealLimitBounds ExtendedRealReciprocalBounds MeasureGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gauge_approximation_threshold]: supporting decreasing
    thresholds r+1/(n+1) for Federer 2.3.8, p. 78 *)
Definition gauge_approximation_threshold (R : realType) (r : R) n :=
  (r + (n.+1%:R)^-1)%R.

(** Source for [gauge_approximation_threshold_strict]: supporting
    strict upper bound on the infimum in Federer 2.3.8, p. 78. *)
Lemma gauge_approximation_threshold_strict (R : realType) (r : R) n :
  (r < gauge_approximation_threshold r n)%R.
Proof. by rewrite /gauge_approximation_threshold ltrDl invr_gt0 ltr0n. Qed.

(** Source for [gauge_approximation_threshold_antitone]: supporting
    monotonicity for increasing superlevels in Federer 2.3.8, p. 78. *)
Lemma gauge_approximation_threshold_antitone (R : realType) (r : R) n m :
  (n <= m)%N -> (gauge_approximation_threshold r m <= gauge_approximation_threshold r n)%R.
Proof.
move=> hnm; rewrite /gauge_approximation_threshold lerD2l.
have hn : (0 < n.+1%:R :> R)%R by rewrite ltr0n.
have hm : (0 < m.+1%:R :> R)%R by rewrite ltr0n.
by rewrite (@lef_pV2 R _ _ hm hn) ler_nat.
Qed.

(** Source for [partial_norm_superlevel_approximation]: supporting
    increasing union identity in the attainment proof of Federer
    2.3.8, p. 78; strict superlevels at r are the union of
    superlevels at thresholds decreasing to r. *)
Lemma partial_norm_superlevel_approximation (R : realType) (X Y : Type)
    (N : Y -> R) (f : partial_function X Y) (r : R) :
  partial_norm_superlevel N f r%:E =
    \bigcup_n partial_norm_superlevel N f (gauge_approximation_threshold r n)%:E.
Proof.
apply/seteqP; split.
- move=> x [y [hy hry]].
  have hd : (0 < N y-r)%R by rewrite subr_gt0; exact hry.
  have [n hn] := positive_reciprocal_nat_small hd.
  exists n=> //; exists y; split=> //.
  change (gauge_approximation_threshold r n < N y)%R.
  rewrite /gauge_approximation_threshold.
  have h : (r + (n.+1%:R)^-1 < r + (N y-r))%R by rewrite ltrD2l.
  by rewrite [(r + (N y-r))%R]addrC subrK in h.
- move=> x [n _ [y [hy hry]]]; exists y; split=> //.
  exact: lt_trans (gauge_approximation_threshold_strict r n) hry.
Qed.

(** Source for [measure_gauge_attained_finite]: direct finite-gauge
    case of Federer 2.3.8, p. 78, second display. Increasing
    continuity, rather than continuity from above with a missing
    finiteness premise, proves the boundary estimate. *)
Lemma measure_gauge_attained_finite (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f : partial_function X Y) (r : R) :
  (forall t : R, measure_measurable mu (partial_norm_superlevel N f t%:E)) ->
  measure_gauge mu N f = r%:E ->
  mu (partial_norm_superlevel N f r%:E) <= r%:E.
Proof.
move=> hme he.
pose F n := partial_norm_superlevel N f (gauge_approximation_threshold r n)%:E.
have hmono n m (hnm : (n <= m)%N) : F n `<=` F m.
  apply: partial_norm_superlevel_antitone; rewrite lee_fin.
  exact: gauge_approximation_threshold_antitone.
have hlim := (@measure_continuity_below R X mu hm F
  (fun n => hme _) hmono).2.
rewrite -partial_norm_superlevel_approximation in hlim.
apply: extended_real_reciprocal_upper_bound=> m.
apply: extended_order_limit_upper_bound hlim _ => n.
pose k := maxn n m.
have hnk : (n <= k)%N by exact: leq_maxl.
have hmk : (m <= k)%N by exact: leq_maxr.
apply: le_trans (@measure_mono R X mu hm _ _ (hmono n k hnk)) _.
have hk : measure_gauge mu N f < (gauge_approximation_threshold r k)%:E.
  rewrite he lte_fin; exact: gauge_approximation_threshold_strict.
have hb := (@measure_gauge_strict_upper_feasible R X Y mu hm N f _ hk).2.
apply: le_trans hb _; rewrite lee_fin.
exact: gauge_approximation_threshold_antitone.
Qed.

(** Source for [measure_gauge_attained]: direct attainment assertion
    of Federer 2.3.8, p. 78. Positive infinity is harmless;
    negative infinity is excluded by nonnegativity of the gauge. *)
Theorem measure_gauge_attained (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f : partial_function X Y) :
  (forall t : R, measure_measurable mu (partial_norm_superlevel N f t%:E)) ->
  measure_gauge_feasible mu N f (measure_gauge mu N f).
Proof.
move=> hme; split; first exact: measure_gauge_nonnegative.
case he: (measure_gauge mu N f)=> [r| |]; first exact (@measure_gauge_attained_finite R X Y mu hm N f r hme he).
- exact: leey.
- have h := measure_gauge_nonnegative mu N f; by rewrite he in h.
Qed.
