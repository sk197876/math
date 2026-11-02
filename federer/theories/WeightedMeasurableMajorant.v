(** Federer (1969), 2.10.24, p. 188, final paragraph: supporting
    measurable-majorant reduction before applying the Borel-partition
    argument of 2.10.8, p. 175. Take the pointwise infimum of countably many
    fine near-minimal weighted covering sums. The infimum is measurable,
    dominates the original input almost everywhere, and is dominated by
    every selected sum. This is a proof expansion, not an assumption that
    the original input is measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBoundsUP ExtendedRealBounds
  PartialFunctionUP PartialFunctionBasic PartialFunctionInfimumUP PartialFunctionInfimumSealed
  MeasurableCountableInfimum MeasurableGraphEquivalence MeasurableFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP WeightedGeneratorIntegral
  WeightedMetricEnvelopeUP WeightedMetricEnvelopeLaws WeightedMetricEnvelope
  WeightedMetricLimitUP WeightedMetricLimit WeightedRestrictionMeasure
  WeightedBorelLevels TopologicalBorel CaratheodoryBorelRegular MetricDiameter NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_generator_sum_measurable]: supporting
    measurability of covering sums for 2.10.24, p. 188,
    by the nonnegative series theorem 2.4.8, p. 84.
    Individual cover members are measure measurable;
    the countable sum may be infinite. *)
Lemma weighted_generator_sum_measurable (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (S : J -> set X) (G : set J) (u : J -> R) :
  is_measure mu -> countable G -> (forall j, G j -> (0<=u j)%R) ->
  (forall j, G j -> measure_measurable mu (S j)) ->
  @is_measure_measurable_function R X (extended_real_line R) mu
    (partial_function_total (weighted_generator_sum S G u)).
Proof.
move=> hm hG hu hS.
have hTS j (hj : G j) : measure_measurable mu (setT `&` S j) by rewrite setTI; exact: hS.
have hi := @weighted_generator_restriction_integral R X J mu S G u setT hm hG hu hTS.
have he : weighted_generator_restriction S G u setT=weighted_generator_sum S G u.
  apply: funext=> x; by rewrite /weighted_generator_restriction in_setT.
by rewrite he in hi; exact: hi.1.
Qed.

(** Source for [weighted_finite_limit_borel_majorant]:
    supporting reduction to a measurable nonnegative input
    in the final paragraph of 2.10.24, p. 188.
    Borel generators give Borel closed superlevels of
    the majorant by countable intersection, as in
    2.3.2(2), p. 73. The selected
    covers keep finite real coefficients; their pointwise
    infimum uses the sealed 2.3.2 infimum interface. *)
Theorem weighted_finite_limit_borel_majorant (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (f : X -> \bar R) (M e : R) :
  is_measure psi -> (forall B, borel_set B -> measure_measurable psi B) ->
  (forall j, borel_set (S j)) ->
  weighted_metric_limit S c psi f=M%:E -> (0<e)%R ->
  exists g : X -> extended_real_line R,
    (forall x, 0<=g x) /\ is_measure_measurable_function psi (partial_function_total g) /\
    (forall t : R, borel_set [set x | t%:E<=g x]) /\
    measure_almost_everywhere psi [set x | f x<=g x] /\
    weighted_metric_limit S c psi g<=(M+e)%R%:E.
Proof.
move=> hm hBorel hS hval he.
pose L := weighted_metric_limit S c psi.
have hL := weighted_metric_limit_specification S c psi.
pose r n := ((n.+1%:R : R)^-1)%R.
have hr n : 0<(r n)%:E by rewrite /r lte_fin invr_gt0 ltr0n.
have hex n : exists G u, is_weighted_metric_cover S psi (r n)%:E f G u /\
    weighted_generator_cost c G u<(M+e)%R%:E.
  have hl := weighted_metric_envelope_specification S c psi (r n)%:E.
  have hh := @weighted_metric_limit_upper R X J S c psi L hL f _ _ (hr n) hl.
  change (is_true (weighted_metric_envelope S c psi (r n)%:E f<=weighted_metric_limit S c psi f)) in hh.
  rewrite hval in hh; apply: weighted_metric_envelope_approximation hl (le_lt_trans hh _).
  rewrite lte_fin ltrDl; exact he.
pose G n := projT1 (cid (hex n)).
pose u n := projT1 (cid (projT2 (cid (hex n)))).
have hGu n := projT2 (cid (projT2 (cid (hex n)))).
pose a n x := (weighted_generator_sum S (G n) (u n) x : extended_real_line R).
pose g x := (extended_real_inf ((fun n=>a n x) @` setT) : extended_real_line R).
have hga x n : g x<=a n x.
  apply: extended_real_inf_lower; by exists n.
have hg0 x : 0<=g x.
  apply: extended_real_inf_greatest=> z [n _ <-]; exact: nonnegative_sum_nonnegative.
pose v := @PartialFunctionInfimum.value R X [the choiceType of (nat : Type)] setT
  (fun n=>partial_function_total (a n)).
have hv := @PartialFunctionInfimum.laws R X [the choiceType of (nat : Type)] setT
  (fun n=>partial_function_total (a n)).
have hveq x y : partial_function_graph v x y <-> g x=y.
  have hvalue z (hz : partial_function_graph v x z) : g x=z.
    apply/eqP; rewrite eq_le; apply/andP; split.
    - apply: (@partial_function_infimum_greatest R X (nat : Type) setT
        (fun n=>partial_function_total (a n)) v hv x z hz (g x))=> w hw.
      change (exists n : nat, setT n /\ a n x=w) in hw.
      have [n [hnD hn]] := hw; rewrite -hn; exact: hga.
    - apply: extended_real_inf_greatest=> w [n _ <-].
      apply: (@partial_function_infimum_lower R X (nat : Type) setT
        (fun n=>partial_function_total (a n)) v hv x z hz (a n x)); exists n=> //.
  split; first exact: hvalue.
  move=> hy.
  have hdom : partial_function_domain v x.
    rewrite (partial_function_infimum_domain hv)=> n _; by exists (a n x).
  have [z hz] := hdom; have hh := hvalue z hz; by rewrite -hy hh.
have hmeas : is_measure_measurable_function psi v.
  apply: (@measurable_countable_infimum R X [the choiceType of (nat : Type)] psi hm setT
    (fun n=>partial_function_total (a n)) v (countableP _) _ hv)=> n _.
  exact: (@weighted_generator_sum_measurable R X J psi S (G n) (u n) hm
    (weighted_metric_cover_countable (hGu n).1) (weighted_metric_cover_nonnegative (hGu n).1)
    (fun j _=>hBorel (S j) (hS j))).
have hgmeas := @measurable_function_graph_equivalent R X (extended_real_line R) psi v
  (partial_function_total g) hveq hmeas.
have hglevel t : borel_set [set x | t%:E<=g x].
  have heq : [set x | t%:E<=g x]=\bigcap_n [set x | t%:E<=a n x].
    apply/seteqP; split.
    - move=> x hx n _; exact: le_trans hx (hga x n).
    - move=> x hx; apply: extended_real_inf_greatest=> z [n _ <-]; exact: hx n Logic.I.
  rewrite heq; apply: (@borel_set_countable_intersection X [the choiceType of (nat : Type)] setT
    (fun n=>[set x | t%:E<=a n x]) (countableP _) (ex_intro _ 0%N Logic.I))=> n _.
  exact: (@countable_weighted_borel_closed_level R X J S (G n) (u n) t
    (weighted_metric_cover_countable (hGu n).1) (weighted_metric_cover_nonnegative (hGu n).1)
    (fun j _=>hS j)).
have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] psi hm setT
  (fun n=>[set x | f x<=a n x]) (countableP _)
  (fun n _=>weighted_metric_cover_dominates (hGu n).1).
have hfg : measure_almost_everywhere psi [set x | f x<=g x].
  apply: (@measure_almost_everywhere_mono R X psi hm _ _ _ hall)=> x hx.
  apply: extended_real_inf_greatest=> z [n _ <-]; exact: hx n Logic.I.
exists g; split=> //; split=> //; split=> //; split=> //.
apply: (weighted_metric_limit_least hL)=> delta lambda hd hl.
have [n hn] := reciprocal_metric_cutoffs_cofinal hd.
have hcov : is_weighted_metric_cover S psi delta g (G n) (u n).
  constructor.
  - exact: weighted_metric_cover_countable (hGu n).1.
  - exact: weighted_metric_cover_nonnegative (hGu n).1.
  - move=> j hj; apply: le_trans (weighted_metric_cover_diameter (hGu n).1 hj) hn.
  - apply: (@measure_almost_everywhere_mono R X psi hm setT _ _
      (measure_almost_everywhere_true hm))=> x _; exact: hga x n.
exact: le_trans (weighted_metric_envelope_lower hl hcov) (ltW (hGu n).2).
Qed.
