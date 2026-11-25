(** Federer (1969), 2.10.47(3), p. 205: translate the null-level open
    covering into small dyadic content on the retained source set. The
    cutoff comparison supplies the finite multiplier. This verifies the
    relative, rather than absolute, cheap-neighbourhood condition required
    by slice continuity. Source context: RealPowerNullNeighborhood.v and
    DyadicContentCutoffUpper.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanClosedBallCompact
  DyadicCubeGridUP DyadicCubeGrid DyadicScaleBounds DyadicContentCutoffUpper
  MetricRealPowerCost MetricRealPowerMeasureUP RealPower RealPowerNullNeighborhood
  RefiningCoverContent HausdorffLengthUP MetricDiameter MetricScaleEnvelope MetricScaleCutoffCost
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_content_null_set_neighbourhood]: supporting
    open covering bound in 2.10.47(3), p. 205.
    The null set A may be a coordinate level of D;
    D is arbitrary inside the root cube. All geometric
    and covering hypotheses have been proved separately. *)
Theorem dyadic_content_null_set_neighbourhood (R : realType) n (a : R_n R n) Q c p i gamma
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (D A : set (inner_metric_space (@euclidean_inner_productP R n))) (e : R) :
  is_dyadic_cube_grid a Q ->
  is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) i gamma ->
  is_metric_real_power_measure c p mu -> (0<n)%N -> (0<c)%R -> (0<p)%R -> (0<e)%R ->
  (forall x, D x -> forall l, (a l<=x l<=a l+1)%R) -> mu A=0 ->
  exists U, [/\ open U, A `<=` U & gamma (D `&` U)<e%:E].
Proof.
move=> hQ hg hmu hn hc hp he hD hz.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose K : R := (((2^n)%N)%:R*real_power (2*Num.sqrt n%:R) p)%R.
have hK : (0<K)%R.
  apply: mulr_gt0; first by rewrite ltr0n expn_gt0.
  apply: real_power_strictly_positive; apply: mulr_gt0; first by rewrite ltr0n.
  by rewrite sqrtr_gt0 ltr0n.
pose nu := metric_scale_envelope (fun S : @nonempty_metric_sets R X=>val S)
  (fun S=>metric_real_diameter_cost c p (val S)) (((2^i)%N)%:R^-1)%:E.
have hnu := metric_scale_envelope_specification (fun S : @nonempty_metric_sets R X=>val S)
  (fun S=>metric_real_diameter_cost c p (val S)) (((2^i)%N)%:R^-1)%:E.
have hbudget : (0<e/K)%R by rewrite divr_gt0.
have [U [hU hAU hsmall]] := @real_power_null_set_cutoff_neighbourhood R X c p
  (((2^i)%N)%:R^-1) (e/K)%R mu nu A
  (fun x r _=>@euclidean_closed_metric_ball_compact R n x r)
  hc hp (dyadic_side_positive R i) hbudget hmu hnu hz.
exists U; split=> //.
have hbound := @dyadic_power_content_cutoff_upper_bound R n a Q c p i gamma nu
  hQ hg hnu hn (ltW hc) hp (D `&` U) (fun x hx=>hD x hx.1).
have hnm := metric_scale_envelope_is_measure hnu
  (fun S=>@metric_real_power_cost_nonnegative R c p (extended_metric_diameter (val S)) (ltW hc)).
have hmono := @measure_mono R X nu hnm (D `&` U) U (fun x hx=>hx.2).
have hK0 : 0<=K%:E by rewrite lee_fin; exact: ltW hK.
have hscaled : K%:E*nu (D `&` U)<=K%:E*nu U := lee_wpmul2l hK0 hmono.
apply: le_lt_trans (le_trans hbound hscaled) _.
have hmul : K%:E*nu U<K%:E*(e/K)%R%:E.
  by rewrite lte_pmul2l ?fin_numE ?lte_fin.
have heq : (K*(e/K)=e)%R by rewrite mulrCA divff ?mulr1 //; exact: lt0r_neq0 hK.
by rewrite -EFinM heq in hmul.
Qed.
