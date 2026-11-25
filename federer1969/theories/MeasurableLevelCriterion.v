(** Federer (1969), 2.3.2(7), pp. 74–75: the numerical separation criterion,
    with its conull-domain premise retained. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology MeasureUP MeasureSplit
  MeasureAlmostUP MeasurableFunctionUP MeasurableSeparationUP MeasurableLevelSeparation
  ReciprocalLevelBands LevelBandTailEstimate LevelComplementCover
  ExtendedRealReciprocalBounds MeasurableExtendedRationalRays.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [level_separation_split_approximation]: supporting
    last estimate of Federer 2.3.2(7), p. 75. We use an
    additive epsilon bound, avoiding undefined subtraction at infinity. *)
Lemma level_separation_split_approximation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (T : set X) (r eps : R) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  is_measure_level_separated mu f -> mu T < +oo -> (0 < eps)%R ->
  mu (T `&` partial_function_preimage f [set y | y <= r%:E]) +
  mu (T `\` partial_function_preimage f [set y | y <= r%:E]) <= mu T + eps%:E.
Proof.
move=> hd hs hT he.
have [N hN] := @level_thin_strip_small R X mu hm f T r eps hs hT he.
have hb : (r < reciprocal_level_endpoint r N)%R.
  by rewrite /reciprocal_level_endpoint ltrDl invr_gt0 ltr0n.
have hc := @level_complement_cover_bound R X mu hm f T r
  (reciprocal_level_endpoint r N) hd.
apply: le_trans (leeD (lexx _) hc) _.
rewrite addeA.
exact: leeD (hs T r _ hb) (ltW hN).
Qed.

(** Source for [level_separation_closed_lower_measurable]: direct conclusion
    that every closed lower level is measurable in Federer 2.3.2(7), p. 75 *)
Lemma level_separation_closed_lower_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (r : R) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  is_measure_level_separated mu f ->
  measure_measurable mu (partial_function_preimage f [set y | y <= r%:E]).
Proof.
move=> hd hs; apply/(measure_measurable_finite_test hm)=> T hT.
have hn := @measure_nonnegative R X mu hm T.
case he : (mu T)=> [t| |] in hT hn *; try by [].
apply: extended_real_reciprocal_upper_bound=> n.
have hp : (0 < ((n.+1)%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
have hTf : mu T < +oo by rewrite he.
have h := @level_separation_split_approximation R X mu hm f T r _ hd hs hTf hp.
by rewrite he -EFinD in h.
Qed.

(** Source for [measurable_extended_level_separation_iff]: direct
    equivalence (7) of Federer 2.3.2, pp. 74–75, for the
    extended-real line. The standing conull-domain hypothesis is explicit;
    no measurability of the separating sets is assumed on the right. *)
Theorem measurable_extended_level_separation_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <-> is_measure_level_separated mu f).
Proof.
move=> hd; split.
- exact: measurable_function_level_separated.
- move=> hs; apply/(measurable_extended_rational_closed_lower_rays_iff hm hd)=> q.
  exact (@level_separation_closed_lower_measurable R X mu hm f (ratr q) hd hs).
Qed.
