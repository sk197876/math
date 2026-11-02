(** Federer (1969), 2.10.2(1), p. 171: restricting to open generators can
    change a size-delta approximation, although the final measures agree.
    This local regression proves the phenomenon using degree zero and [0,1]
    on the real line, instead of the printed degree-one circle example. The
    change of example is explicit; no circle calculation is claimed here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground MetricDiameterUP MetricDiameter
  MetricDiameterReal HausdorffLengthUP HausdorffMeasureUP HausdorffDiameterCost
  MetricScaleEnvelopeUP MetricScaleEnvelope NonnegativeSum NonnegativeSumSupport TwoTermSumBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_unit_diameter_cannot_contain_both_endpoints]:
    supporting geometric obstruction for the local alternative
    example of Federer 2.10.2(1), p. 171. An open
    real set containing 0 and 1 has diameter strictly
    larger than one. This lemma is not separately printed. *)
Lemma open_unit_diameter_cannot_contain_both_endpoints (R : realType)
    (U : set (real_line_metric R)) : open U -> extended_metric_diameter U<=1 ->
  U 0%R -> U 1%R -> False.
Proof.
move=> ho hd h0 h1; rewrite openE in ho.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP ((0:R)%R : real_line_metric R) U) (ho (0:R)%R h0).
have hehalf : (0<e/2)%R by rewrite divr_gt0 // ltr0n.
have hhalf : (e/2<e)%R by lra.
have hz : U (-(e/2))%R.
  apply: hball; change (is_true (`|0-(-(e/2))|<e)%R).
  by rewrite sub0r opprK (ger0_norm (ltW hehalf)).
have hh := le_trans (metric_diameter_upper (extended_metric_diameter_specification U) h1 hz) hd.
have hp : (0<1+e/2)%R by lra.
rewrite real_line_metric_distanceE opprK (gtr0_norm hp) lee_fin in hh.
have hlt : (1<1+e/2)%R by rewrite ltrDl.
by have := lt_le_trans hlt hh; rewrite ltxx.
Qed.

(** Source for [hausdorff_zero_scale_nonempty_bound]:
    supporting degree-zero infimum calculation for the
    local alternative example of Federer 2.10.2(1),
    p. 171. A nonempty set of admissible diameter
    has unrestricted size-delta mass exactly one. *)
Lemma hausdorff_zero_scale_nonempty_bound (R : realType) (X : metricType R)
    (A : set X) (delta : \bar R) : A !=set0 -> extended_metric_diameter A<=delta ->
  metric_scale_envelope (fun j : @nonempty_metric_sets R X => val j)
    (fun j => hausdorff_diameter_cost 0 (val j)) delta A = 1.
Proof.
move=> hA hd.
pose j : @nonempty_metric_sets R X :=
  @exist _ (fun B : set X => B \in [set B | B !=set0]) A (mem_set hA).
have hn := @metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost 0 (val j)) delta.
apply/eqP; rewrite eq_le; apply/andP; split.
- have hcov : A `<=` \bigcup_(k in [set j]) val k by move=> x hx; exists j.
  have hsize k : [set j] k -> extended_metric_diameter (val k)<=delta by move=> ->.
  have hh := @metric_scale_envelope_lower R X (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => hausdorff_diameter_cost 0 (val j)) delta _ hn
    A [set j] (countable1 j) hsize hcov.
  rewrite nonnegative_sum_singleton in hh; last exact: hausdorff_diameter_cost_nonnegative.
  by rewrite hausdorff_diameter_cost_zero_degree in hh.
- apply: (metric_scale_envelope_greatest hn)=> G hG hsize hcov.
  have [x hx] := hA; have [k hk _] := hcov x hx.
  have hh := @nonnegative_sum_term R (@nonempty_metric_sets R X) G
    (fun k => hausdorff_diameter_cost 0 (val k)) k hk.
  by rewrite hausdorff_diameter_cost_zero_degree in hh.
Qed.

(** Source for [hausdorff_open_cutoff_differs]: explicit
    local alternative to the circle in Federer 2.10.2(1),
    p. 171. At degree zero and cutoff one, [0,1]
    has unrestricted mass one, whereas every open cover
    uses at least two distinct generators and costs at
    least two. The final measures still agree by the
    separate open-cover equality theorem. *)
Theorem hausdorff_open_cutoff_differs (R : realType) :
  let A : set (real_line_metric R) := `[(0:R)%R,(1:R)%R] in
  metric_scale_envelope (fun j : @nonempty_metric_sets R (real_line_metric R) => val j)
    (fun j => hausdorff_diameter_cost 0 (val j)) 1 A = 1 /\
  (2:R)%:E<=metric_scale_envelope (fun j : @nonempty_open_metric_sets R (real_line_metric R) => val j)
    (fun j => hausdorff_diameter_cost 0 (val j)) 1 A.
Proof.
move=> A.
have h0 : A 0%R by rewrite /A /= in_itv /= lexx ler01.
have h1 : A 1%R by rewrite /A /= in_itv /= lexx ler01.
split.
- apply: hausdorff_zero_scale_nonempty_bound; first by exists 0%R.
  by rewrite /A (extended_metric_diameter_segment (@ler01 R)) subr0.
- have hn := @metric_scale_envelope_specification R (real_line_metric R)
    (@nonempty_open_metric_sets R (real_line_metric R))
    (fun j => val j) (fun j => hausdorff_diameter_cost 0 (val j)) 1.
  apply: (metric_scale_envelope_greatest hn)=> G hG hsize hcov.
  have [j0 hj0 hx0] := hcov 0%R h0.
  have [j1 hj1 hx1] := hcov 1%R h1.
  have hne : j0!=j1.
    apply/eqP=> he; have hx1' : val j0 1%R by rewrite he.
    exact (@open_unit_diameter_cannot_contain_both_endpoints R (val j0)
      (set_valP j0).1 (hsize j0 hj0) hx0 hx1').
  have hh := @nonnegative_sum_two_term_bound R (@nonempty_open_metric_sets R (real_line_metric R))
    G (fun j => hausdorff_diameter_cost 0 (val j)) j0 j1 hj0 hj1 hne.
  by rewrite !hausdorff_diameter_cost_zero_degree in hh.
Qed.
