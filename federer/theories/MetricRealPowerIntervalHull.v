(** Federer (1969), 2.10.28, p. 191: the real-line power measure may be
    studied with compact interval generators. A nonempty set of finite
    diameter lies in a compact interval of that same diameter and cost. This
    supporting hull fact expands 2.10.2(1), p. 171, using the real infimum,
    without requiring the original set to be closed or to attain either
    endpoint. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameterUP MetricDiameter MetricDiameterReal
  CompactIntervalGauge RealPower MetricRealPowerCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_cover_interval_exists]: supporting
    same-diameter compact interval replacement
    for the real-line assertion in 2.10.28,
    p. 191. Existence uses [inf S,inf S+d]
    with d the finite actual diameter. The
    coefficient and exponent remain explicit;
    no Gamma normalisation is assumed. *)
Theorem real_power_cover_interval_exists (R : realType) (c p : R)
    (S : set (real_line_metric R)) :
  S !=set0 -> @extended_metric_diameter R [the metricType R of real_line_metric R] S< +oo ->
  exists T : compact_real_intervals R,
    S `<=` val T /\
    @extended_metric_diameter R [the metricType R of real_line_metric R] (val T)=extended_metric_diameter S /\
    (concave_interval_cost (fun x=>(c*real_power x p)%R) (val T))%:E=metric_real_diameter_cost c p S.
Proof.
move=> hS hfin.
pose D := @extended_metric_diameter R [the metricType R of real_line_metric R] S.
pose d := fine D.
have hD0 : 0<=D := metric_diameter_nonnegative (extended_metric_diameter_specification S).
have hDnum : D \is a fin_num by rewrite (ge0_fin_numE hD0).
have hD : D=d%:E := esym (fineK hDnum).
have hd : (0<=d)%R by move: hD0; rewrite hD lee_fin.
have hdist x y : S x -> S y -> (`|x-y|<=d)%R.
  move=> hx hy; have hh := metric_diameter_upper (extended_metric_diameter_specification S) hx hy.
  by rewrite real_line_metric_distanceE -/D hD lee_fin in hh.
have hhull := @real_bounded_diameter_interval_hull R S d hS hdist.
have hord : (inf S<=inf S+d)%R by rewrite lerDl.
have hI : is_compact_real_interval (`[inf S,(inf S+d)%R] : set (real_line_metric R)).
  exists (inf S),(inf S+d)%R; by split.
pose T : compact_real_intervals R := Sub (`[inf S,(inf S+d)%R] : set (real_line_metric R)) (mem_set hI).
have hdiam : @extended_metric_diameter R [the metricType R of real_line_metric R] (val T)=d%:E.
  by rewrite /T /= (extended_metric_diameter_segment hord) addrAC subrr add0r.
exists T; split; first exact hhull.
split; first by rewrite hdiam -hD.
rewrite /metric_real_diameter_cost -/D hD metric_real_power_cost_finite /concave_interval_cost hdiam; by [].
Qed.
