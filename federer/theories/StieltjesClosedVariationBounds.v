(** Federer (1969), 2.9.19, p. 164: compare the sum of the two
    induced-measure masses with the arc-length increment, using 2.5.17, p.
    111. Continuity at the two endpoints removes their atoms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesIntegral
  StieltjesImageMeasures StieltjesInducedPairLaws StieltjesContinuityPoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [stieltjes_closed_pair_variation_bound]: supporting sum
    estimate used in Federer 2.9.19, p. 164 At continuity endpoints a,b, the
    induced measures have no endpoint atoms, so the open-interval variation
    bound of 2.5.17 applies to the closed interval as well. The total
    variation is the arc-length increment. *)
Lemma stieltjes_closed_pair_variation_bound (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> a<=b ->
  g @ a --> g a -> g @ b --> g b ->
  (psip `[a,b]+psim `[a,b]<=(arc_length (g : R -> real_line_metric R) b-
    arc_length (g : R -> real_line_metric R) a)%:E)%E.
Proof.
move=> hg hp hab hca hcb.
have [hmp [hmm [_ [_ [_ [_ [_ [_ [_ [hOpen [hPoint _]]]]]]]]]]] :=
  @induced_measure_pair_laws R g hg psip psim hp.
have [hPa hMa] := hPoint a hca.
have [hPb hMb] := hPoint b hcb.
rewrite (@measure_segment_open_interval R psip a b hmp hPa hPb)
  (@measure_segment_open_interval R psim a b hmm hMa hMb).
have heq : total_variation g a b=
    arc_length (g : R -> real_line_metric R) b-arc_length (g : R -> real_line_metric R) a.
  by rewrite /total_variation -(@arc_length_increment R [the metricType R of real_line_metric R] g hg a b hab).
rewrite -heq; exact: hOpen a b hab.
Qed.
