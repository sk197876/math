(** A lower spherical-mass bound for the actual image in the project
    test of Federer 2.10.11, p. 176. Twice the existing binary
    probability is bounded by every target ball's actual diameter cost. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import BinaryPrefixMetric BinaryPrefixProbability BinaryVerticalEmbedding
  MetricProductBackground RealMetricBackground MetricClosedBalls MetricDiameter
  HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost CaratheodoryGeneratorMeasureBound
  MeasureUP MeasureBasic MeasurePushforward FiniteMeasureScaling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [binary_vertical_spherical_mass_lower]: the actual
    image has spherical length at least two, in the project test
    of Federer 2.10.11, p. 176. The lower bound is obtained by
    generator comparison with a proved probability, without assuming
    measurability or an exact value for an arbitrary covering infimum. *)
Theorem binary_vertical_spherical_mass_lower (R:realType):
  2%:E<=@spherical_measure R
    (metric_product (binary_prefix_metric R) (real_line_metric R)) 1
    ((@binary_vertical_embedding R) @` setT).
Proof.
pose X:=binary_prefix_metric R.
pose Y:=metric_product X (real_line_metric R).
pose f:=@binary_vertical_embedding R.
pose mu:=@binary_prefix_probability R.
pose eta:=fun B:set Y=>2%R%:E*measure_pushforward f mu B.
have hm:is_measure mu:=binary_prefix_probability_measure R.
have he:is_measure eta:=@finite_scale_is_measure R Y
  (measure_pushforward f mu) (measure_pushforward_is_measure f hm) 2 (ler0n R 2).
have hgen (j:@positive_closed_metric_balls R Y):
    eta (val j)<=hausdorff_diameter_cost 1 (val j).
  have [a [r [hr hB]]]:=set_valP j.
  have hEqual:val j=metric_closed_ball a r.
    apply/seteqP;split=> z hz;[exact:(hB z).1 hz|exact:(hB z).2 hz].
  have hpre:f @^-1` (metric_closed_ball a r) `<=` metric_closed_ball a.1 r.
    move=> x hx.
    have h:(Order.max (mdist a.1 x) (mdist a.2 (0%R:real_line_metric R))<=r)%R:=hx.
    by move:h;rewrite ge_max=>/andP [h _].
  have hb:=@measure_mono R X mu hm _ _ hpre.
  have hball:=@binary_prefix_probability_ball R a.1 r hr.
  rewrite hEqual hausdorff_diameter_cost_one_degree
    (@binary_vertical_ball_diameter R a r (ltW hr)).
  rewrite /eta /measure_pushforward.
  have htwo:0<=(2:R)%:E by rewrite lee_fin ler0n.
  have hscaled:=lee_wpmul2l htwo (le_trans hb hball).
  apply:le_trans hscaled _.
  rewrite -EFinM lee_fin;by rewrite mulr_natl mulr2n.
have hbound:=@measure_bounded_by_caratheodory_generators R Y
  (@positive_closed_metric_balls R Y) (fun j=>val j)
  (fun j=>hausdorff_diameter_cost 1 (val j)) eta (@spherical_measure R Y 1)
  he (@spherical_measure_specification R Y 1) hgen (f @` setT).
have hpreimage:f @^-1` (f @` setT)=setT.
  apply/seteqP;split=> // x _;by exists x.
by rewrite /eta /measure_pushforward hpreimage /mu
  binary_prefix_probability_whole mule1 in hbound.
Qed.
