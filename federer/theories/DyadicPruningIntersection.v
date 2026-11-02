(** Federer (1969), 2.10.47, p. 205, final paragraph: the nested
    intersection has finite positive measure. The upper bound uses the
    cofinal dyadic cutoffs; the positive lower bound uses compact-cost
    continuity from 2.10.20. The sequence is used only through its abstract
    pruning laws. Source context: DyadicPruningUP.v and
    RealPowerCompactCost.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGrid DyadicPruningUP CompactContentPruning
  DyadicContentLimitBound DyadicContentCutoffUpper DyadicContentFinite DyadicScaleBounds
  RefiningCoverContent MetricDiameter MetricRealPowerCost MetricRealPowerMeasureUP
  RealPower RealPowerCompactCost RealPowerCompactCutoff CompactCostOpenEnvelope
  EuclideanClosedBallCompact LipschitzFunctionCompact CaratheodoryLimitUP
  HausdorffLengthUP MetricScaleEnvelopeUP MetricScaleEnvelope MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_pruning_finite_positive_intersection]:
    both final bounds for the intersection in 2.10.47,
    p. 205, for positive real power and coefficient.
    All cutoff comparisons and compact-cost continuity
    hypotheses are proved here from their specifications. *)
Theorem dyadic_pruning_finite_positive_intersection (R : realType) n (a : R_n R n) Q c p
    (gamma : nat -> set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    mu h (A : set (inner_metric_space (@euclidean_inner_productP R n))) E :
  is_dyadic_cube_grid a Q ->
  (forall i, is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) i (gamma i)) ->
  is_metric_real_power_measure c p mu -> (0<n)%N -> (0<c)%R -> (0<p)%R ->
  (forall x, A x -> forall l, (a l<=x l<=a l+1)%R) ->
  is_dyadic_compact_pruning gamma h A E -> 0<gamma h A ->
  exists B, [/\ compact B, B `<=` A, 0<mu B & mu B< +oo].
Proof.
move=> hQ hg hmu hn hc hp hroot hE hpos.
pose X := inner_metric_space (@euclidean_inner_productP R n).
have hinit := dyadic_pruning_initial hE.
have hpr := dyadic_pruning_content_laws hE.
pose B := \bigcap_j E j.
have [hBc hBE] := content_pruning_intersection_compact hpr.
have hBA : B `<=` A by rewrite -hinit.
have hcost (T : set X) : 0<=metric_real_diameter_cost c p T :=
  @metric_real_power_cost_nonnegative R c p (extended_metric_diameter T) (ltW hc).
have hgm i := refining_cover_content_measure (hg i) (fun T _=>hcost T).
have hfin := @dyadic_power_content_root_finite R n a Q c p h (gamma h) hQ (hg h)
  (ltW hc) (ltW hp) A hroot.
have hnum : gamma h A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative (hgm h) A)).
pose v := fine (gamma h A).
have hvE : gamma h A=v%:E := esym (fineK hnum).
have hv : (0<v)%R by move: hpos; rewrite hvE lte_fin.
have hupper : mu B<=gamma h A.
  apply: (@dyadic_contents_bound_power_measure R n a Q c p gamma mu h B (gamma h A)
    hQ hg hmu (ltW hc))=> j.
  rewrite -(@content_pruning_mass R X _ _ E hpr j j (leqnn j)).
  apply: (@measure_mono R X _ (hgm (h+j)%N))=> x hx; exact: hx j Logic.I.
pose K : R := (((2^n)%N)%:R*real_power (2*Num.sqrt n%:R) p)%R.
have hK : (0<K)%R.
  apply: mulr_gt0; first by rewrite ltr0n expn_gt0.
  apply: real_power_strictly_positive; apply: mulr_gt0; first by rewrite ltr0n.
  by rewrite sqrtr_gt0 ltr0n.
pose d : R := (((2^h)%N)%:R^-1)%R.
have hd : (0<d)%R := dyadic_side_positive R h.
pose S := fun T : @nonempty_metric_sets R X=>val T.
pose cost := fun T : @nonempty_metric_sets R X=>metric_real_diameter_cost c p (val T).
pose large := metric_scale_envelope S cost d%:E.
pose small := metric_scale_envelope S cost ((d/2)%R)%:E.
have hl := metric_scale_envelope_specification S cost d%:E.
have hs := metric_scale_envelope_specification S cost ((d/2)%R)%:E.
have hX : metric_boundedly_compact X := fun x r _=>@euclidean_closed_metric_ball_compact R n x r.
have hhalf : (0<d/2)%R by apply: divr_gt0=> //; rewrite ltr0n.
have hhalflt : (d/2<d)%R by rewrite ltr_pdivrMr ?ltr0n //; rewrite mulr_natr mulr2n ltrDl.
have hlc := @real_power_compact_cutoff_laws R X c p d large hX (ltW hc) (ltW hd) hl.
have hsc := @real_power_compact_cutoff_laws R X c p (d/2)%R small hX (ltW hc) (ltW hhalf) hs.
have hlow j : ((v/K)%R)%:E<=large (E j).
  have hEA : E j `<=` A.
    rewrite -hinit; exact: (@content_pruning_nested R X _ _ E hpr 0%N j (leq0n j)).
  have hEr x (hx : E j x) := hroot x (hEA x hx).
  have hh := @dyadic_power_content_cutoff_upper_bound R n a Q c p h (gamma h) large
    hQ (hg h) hl hn (ltW hc) hp (E j) hEr.
  have hmass := @content_pruning_mass R X _ _ E hpr 0%N j (leq0n j).
  rewrite addn0 in hmass; rewrite hmass hvE in hh.
  have hKi : 0<=((K^-1)%R)%:E by rewrite lee_fin invr_ge0; exact: ltW hK.
  have hh' := lee_wpmul2l hKi hh.
  change (is_true (((K^-1)%R)%:E*v%:E<=((K^-1)%R)%:E*(K%:E*large (E j)))) in hh'.
  rewrite muleA -!EFinM mulVf ?gt_eqF // mul1e mulrC in hh'.
  exact hh'.
have hbound := @compact_cost_decreasing_intersection_bound R X
  (real_power_compact_generator_cost c p) (@real_power_compact_generator_cost_laws R X c p hc hp)
  (d/2)%R d small large E ((v/K)%R)%:E hX hhalflt hsc hlc
  (content_pruning_compact hpr) (content_pruning_nested hpr) hlow.
have hsmall := @caratheodory_limit_upper R X _ S cost mu hmu B ((d/2)%R)%:E small
  (ltac:(by rewrite lte_fin)) hs.
have hpositive : 0<((v/K)%R)%:E by rewrite lte_fin; exact: divr_gt0 hv hK.
exists B; split=> //.
- exact: lt_le_trans hpositive (le_trans hbound hsmall).
- exact: le_lt_trans hupper hfin.
Qed.
