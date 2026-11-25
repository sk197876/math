(** Federer (1969), 2.10.28, p. 193: the cumulative function's increment
    bound follows from (3). Work with any set A having that interval bound,
    and the abstract finite cumulative specification of psi restricted to A. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP
  ConcaveIntervalMeasure MeasureUP MeasureBasic MeasureRestriction TopologicalBorel BorelRegularMeasureUP CountableOrderIntervals
  FiniteCumulativeFunctionUP FiniteCumulativeFunctionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [concave_interval_distribution_increment_bound]: direct
    0<=f(b)-f(a)<=h(b-a) in 2.10.28, p. 193,
    before the power-gauge specialisation. The
    increment measures A intersect (a,b], which
    lies in the closed test interval [a,b]. *)
Theorem concave_interval_distribution_increment_bound (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (A : set (real_line_metric R)) (f : R -> R) :
  is_finite_cumulative_function (measure_restrict (concave_interval_measure h) A) f ->
  (forall T : compact_real_intervals R, (concave_interval_measure h (A `&` val T)<=
    (concave_interval_cost h (val T))%:E)%E) ->
  forall a b, a<=b -> 0<=f b-f a /\ f b-f a<=h (b-a).
Proof.
move=> hf hbound a b hab.
pose mu := concave_interval_measure h.
pose nu := measure_restrict mu A.
have hm := concave_interval_measure_is_measure hg.
have hn : is_measure nu := measure_restrict_is_measure hm A.
have hmono := @finite_cumulative_function_nondecreasing R nu hn f hf a b hab.
split; first by rewrite subr_ge0.
have hray : measure_measurable nu [set z : R | z<=a].
  apply: measure_restrict_measurable.
  apply: (@borel_regular_borel_measurable R (real_line_metric R) mu hm
    (@concave_interval_measure_borel_regular R h hg)).
  apply: closed_borel_set; exact: order_closed_lower_ray_closed.
have hinc := @finite_cumulative_function_increment R nu hn f hf a b hab hray.
have hTab : is_compact_real_interval (`[a,b] : set (real_line_metric R)) by exists a,b; split.
pose T : compact_real_intervals R := Sub (`[a,b] : set (real_line_metric R)) (mem_set hTab).
have hsub : A `&` ([set z : R | z<=b] `\` [set z : R | z<=a]) `<=` A `&` val T.
  move=> z [hzA [hzb /negP hza]]; split=> //.
  rewrite /T /= in_itv /= hzb andbT.
  by apply: ltW; rewrite ltNge.
have hh := le_trans (@measure_mono R (real_line_metric R) mu hm _ _ hsub) (hbound T).
change (is_true (nu ([set z : R | (z<=b)%R] `\` [set z : R | (z<=a)%R])<=
  (concave_interval_cost h (val T))%:E)%E) in hh.
by rewrite hinc /T /= (concave_interval_cost_segment h hab) lee_fin in hh.
Qed.

(** Source for [concave_interval_distribution_modulus]: supporting
    continuity of f from the displayed increment
    estimate in 2.10.28, p. 193. Relative
    continuity of h at zero supplies one
    uniform radius for both orders of a,b. *)
Theorem concave_interval_distribution_modulus (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (f : R -> R) :
  (forall a b, a<=b -> 0<=f b-f a /\ f b-f a<=h (b-a)) ->
  forall e : R, 0<e -> exists d : R, 0<d /\
    forall a b, `|b-a|<d -> `|f b-f a|<e.
Proof.
move=> hb e he.
have [d [hd hnear]] := @interval_gauge_continuity R h hg 0 e (lexx 0) he.
exists d; split=> // a b habs.
case: (leP a b)=> hab.
- have [hnon hbound] := hb a b hab.
  rewrite ger0_norm //; apply: le_lt_trans hbound _.
  have hlen : 0<=b-a by rewrite subr_ge0.
  have hh := hnear (b-a) hlen.
  rewrite subr0 in hh; have heh := hh habs.
  rewrite (interval_gauge_zero hg) subr0 in heh.
  exact: le_lt_trans (ler_norm (h (b-a))) heh.
- have hba := ltW hab.
  have [hnon hbound] := hb b a hba.
  rewrite distrC ger0_norm //; apply: le_lt_trans hbound _.
  have hsmall : `|a-b|<d by rewrite distrC.
  have hlen : 0<=a-b by rewrite subr_ge0.
  have hh := hnear (a-b) hlen.
  rewrite subr0 in hh; have heh := hh hsmall.
  rewrite (interval_gauge_zero hg) subr0 in heh.
  exact: le_lt_trans (ler_norm (h (a-b))) heh.
Qed.

(** Source for [concave_interval_distribution_continuous]: direct continuity
    of f inferred in 2.10.28, p. 193 The proof uses only the proved gauge
    modulus and the existing real topology. *)
Theorem concave_interval_distribution_continuous (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (f : R -> R) :
  (forall a b, a<=b -> 0<=f b-f a /\ f b-f a<=h (b-a)) ->
  continuous (f : real_line_metric R -> real_line_metric R).
Proof.
move=> hb x; apply/cvg_ballP=> e he.
have [d [hd hnear]] := @concave_interval_distribution_modulus R h hg f hb e he.
apply: (@filterS (real_line_metric R) (nbhs x) (nbhs_filter x)
  (ball x d) (f @^-1` ball (f x) e) _ (nbhsx_ballx x d hd))=> y.
rewrite /= !real_line_ball_distance /= => hxy.
rewrite distrC; apply: hnear; by rewrite distrC.
Qed.
