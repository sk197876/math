(** Federer (1969), 2.10.39, printed p. 199: use the enclosing box of
    2.10.38 and its attained initial exterior products to replace the box
    side product by the exterior-diameter cost. This supporting generator
    bound retains a strict relationship between source and spherical
    cutoffs. It allows compact nonconvex sources and zero widths. Source
    context: RectangularSphericalCover.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  FinitePrefixes EuclideanBoxUP GreedyChordFrameUP GreedyChordFrame
  GreedyChordFrameLaws GreedyChordDiameterBound GreedyChordEnclosingBox GreedyChordExteriorProducts
  RectangularSphericalCover HausdorffMeasureUP HausdorffDiameterCost
  MetricScaleEnvelopeUP MetricScaleEnvelopeLaws MetricDiameter ExteriorMeasureGauge
  ExteriorDiameterUP ExteriorDiameter ExteriorDiameterLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_exterior_spherical_cutoff_bound]: supporting
    compact-generator comparison for 2.10.39, p. 199.
    For positive degree m=p+1 at most n, the
    spherical cutoff cost is bounded by n^(m/2)
    2^(m-1) times the actual exterior cost. The
    source and target cutoffs need not be equal. *)
Theorem compact_exterior_spherical_cutoff_bound (R : realType) n p
    (hp : (p<n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (t d : R)
    (nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :
  compact S -> S !=set0 ->
  (extended_metric_diameter S<=t%:E)%E -> Num.sqrt n%:R*t<d ->
  is_metric_scale_envelope
    (fun j : @positive_closed_metric_balls R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]=>val j)
    (fun j=>hausdorff_diameter_cost p.+1 (val j)) d%:E nu ->
  (nu S<=((Num.sqrt n%:R)^+p.+1*2^+p)%:E*exterior_diameter_cost p.+1 S)%E.
Proof.
move=> hS hne hdiam hcap hn.
pose D := @compact_greedy_chord_frame R n S hS hne.
have hD := @compact_greedy_chord_frame_specification R n S hS hne.
have [origin [Q [hQ hSQ]]] := greedy_chord_enclosing_box hD.
have hw := greedy_chord_length_diameter_bound hD hdiam (Ordinal hp).
have hmesh : Num.sqrt n%:R*greedy_chord_length D (Ordinal hp)<d.
  exact: le_lt_trans (ler_wpM2l (sqrtr_ge0 _) hw) hcap.
have hbox := @rectangular_spherical_cutoff_bound R n p hp origin
  (greedy_chord_axis D) (greedy_chord_length D) Q d nu hQ
  (greedy_chord_lengths_ordered hD) hmesh hn.
have hsub : (nu S<=nu Q)%E := metric_scale_envelope_mono hn hSQ.
pose P := \prod_(i<p.+1) family_prefix hp (greedy_chord_length D) i.
have hprod : (P%:E<=extended_exterior_diameter p.+1 S)%E.
  rewrite /P -(greedy_chord_prefix_norm hD hp).
  apply: (exterior_diameter_endpoint_upper (extended_exterior_diameter_specification p.+1 S)).
  - move=> i; exact: (greedy_chord_endpoints_law hD (widen_ord hp i)).1.
  - move=> i; exact: (greedy_chord_endpoints_law hD (widen_ord hp i)).2.
pose C : R := (Num.sqrt n%:R)^+p.+1*2^+p.
have hC : 0<=C by apply: mulr_ge0; apply: exprn_ge0; [exact: sqrtr_ge0|exact: ler0n].
have hh0 : 0<=hausdorff_normalisation R p.+1*C :=
  mulr_ge0 (ltW (hausdorff_normalisation_positive R p.+1)) hC.
have hcoeff0 : (0<=(hausdorff_normalisation R p.+1*C)%:E)%E by rewrite lee_fin.
have hh := lee_wpmul2l hcoeff0 hprod.
have hfold : (C%:E*exterior_diameter_cost p.+1 S)%E=
    ((hausdorff_normalisation R p.+1*C)%:E*extended_exterior_diameter p.+1 S)%E.
  by rewrite /exterior_diameter_cost muleA -EFinM (mulrC C).
rewrite -hfold -EFinM mulrA in hh.
exact: le_trans (le_trans hsub hbox) hh.
Qed.
