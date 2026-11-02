(** Supporting zero atoms for Federer (1969), 2.10.7, p. 174: every
    positive-cutoff approximation vanishes at each continuity point of g.
    Enclose the point in a short interval whose raw g-increment is
    arbitrarily small. We use the printed Federer raw increment of
    StieltjesCaratheodoryUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground StieltjesCaratheodoryUP StieltjesIntervalBounds
  MetricScaleEnvelopeUP MetricScaleEnvelopeLaws MetricScaleCutoffCost
  MetricDiameter MetricScaleMeasureBound MetricScaleWeightedBound CaratheodoryBorelRegular MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [stieltjes_scale_small_interval_bound]:
    supporting single-generator bound in Federer
    2.10.7, p. 174. A bounded interval
    below the cutoff has approximation mass
    at most its printed raw increment. *)
Lemma stieltjes_scale_small_interval_bound (R : realType) (g : R -> R)
    (delta : \bar R) (nu : set (real_line_metric R) -> \bar R) (a b : R) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) ->
  is_metric_scale_envelope (@stieltjes_interval_set R) (stieltjes_interval_cost g) delta nu ->
  (a<b)%R -> (b-a)%R%:E<=delta -> nu `]a,b[<=(g b-g a)%:E.
Proof.
move=> hg hnu hab hd.
pose j := @stieltjes_interval_index R a b hab.
have hj := le_trans (stieltjes_interval_diameter_bound j) hd.
exact: (@metric_scale_generator_bound R [the metricType R of real_line_metric R]
  (stieltjes_open_intervals R) (@stieltjes_interval_set R) (stieltjes_interval_cost g)
  delta nu j hnu (stieltjes_interval_cost_nonnegative hg j) hj).
Qed.

(** Source for [stieltjes_scale_continuity_point_null]:
    supporting null continuity-point atom for
    every positive size cutoff in Federer
    2.10.7, p. 174. No global continuity
    or right-continuity convention is imposed
    on the nondecreasing integrator. *)
Theorem stieltjes_scale_continuity_point_null (R : realType) (g : R -> R)
    (delta : \bar R) (nu : set (real_line_metric R) -> \bar R) (c : R) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) ->
  is_metric_scale_envelope (@stieltjes_interval_set R) (stieltjes_interval_cost g) delta nu ->
  0<delta -> g @ c --> g c -> nu [set c]=0.
Proof.
move=> hg hnu hdelta hcont.
have hm := metric_scale_envelope_is_measure hnu (stieltjes_interval_cost_nonnegative hg).
apply/eqP; rewrite eq_le (measure_nonnegative hm [set c]) andbT.
apply/lee_addgt0Pr=> e he; rewrite add0e.
have he4 : (0<e/4)%R by rewrite divr_gt0 // ltr0n.
have hn : nbhs c (g @^-1` ball (g c) (e/4)%R).
  exact: (cvg_ballP _ _).1 hcont (e/4)%R he4.
have [sigma hsigma hball] := (nbhs_ballP _ _).1 hn.
have [k hk] := reciprocal_metric_cutoffs_cofinal hdelta.
pose d : R := (((k.+1)%:R)^-1)%R.
have hd : (0<d)%R by rewrite /d invr_gt0 ltr0n.
pose r := Order.min (sigma/2)%R (d/4)%R.
have hr : (0<r)%R by rewrite /r lt_min !divr_gt0 ?ltr0n.
have hrsigma : (r<=sigma/2)%R by rewrite /r ge_min lexx.
have hrd : (r<=d/4)%R by rewrite /r ge_min lexx orbT.
pose a := (c-r)%R; pose b := (c+r)%R.
have hab : (a<b)%R by rewrite /a /b; lra.
have haNear : (`|c-a|<sigma)%R.
  have heq : (c-a=r)%R by rewrite /a; lra.
  rewrite heq ger0_norm //; lra.
have hbNear : (`|c-b|<sigma)%R.
  have heq : (c-b= -r)%R by rewrite /b; lra.
  rewrite heq normrN ger0_norm //; lra.
have haG : (`|g c-g a|<e/4)%R := hball a haNear.
have hbG : (`|g c-g b|<e/4)%R := hball b hbNear.
have hga : (g c-g a<e/4)%R := le_lt_trans (ler_norm _) haG.
have hgb : (g b-g c<e/4)%R.
  apply: le_lt_trans (ler_norm _) _.
  by rewrite -[(g b-g c)%R]opprB normrN.
have hcost : (g b-g a<e)%R by lra.
have hsize : (b-a)%R%:E<=delta.
  apply: le_trans _ hk; rewrite lee_fin.
  change (is_true (b-a<=d)%R); rewrite /a /b; lra.
have hinc : [set c] `<=` (`]a,b[ : set (real_line_metric R)).
  move=> x ->; rewrite /= in_itv /= /a /b; apply/andP; split; lra.
have hsmall := @stieltjes_scale_small_interval_bound R g delta nu a b hg hnu hab hsize.
apply: ltW; apply: le_lt_trans (le_trans (measure_mono hm hinc) hsmall) _.
by rewrite lte_fin.
Qed.
