(** Federer (1969), 3.2.46, p. 281, last sentence:
    the volume derivate at a is sqrt(discr g(a)). This
    supporting measure lemma proves the pointwise conclusion
    from a continuous positive density, without a global
    bounded-finite measure premise or an exceptional null set. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic RegularMeasureUP
  MeasureDensityUP NonnegativeDensitySetLowerBound NonnegativeDensitySetUpperBound
  MeasureDerivates CoveringRelationUP CoveringRelationFineness CoveringRelationLimits
  CoveringFiniteLimitBounds MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_finite_containing_relation]: the
    positive finite denominator cells containing their base
    point, supporting the local derivate assertion in 3.2.46,
    p. 281. This includes ordinary sufficiently small balls;
    zero denominator and infinity/infinity are not completed. *)
Definition positive_finite_containing_relation (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (a : X) (S : set X) :=
  S a /\ (0<phi S)%E /\ phi S \is a fin_num.

(** Source for [continuous_positive_density_derivate]: the
    local volume-derivate argument of 3.2.46, p. 281,
    expanded using 2.9.1, p. 153. On every fine family of
    positive finite cells containing a, the density-measure
    ratio tends to its actual continuous positive value h(a).
    Every point is retained; no almost-everywhere weakening. *)
Theorem continuous_positive_density_derivate (R : realType) (X : metricType R)
    (phi mu : set X -> \bar R) (h : X -> real_line_metric R) a :
  is_measure phi -> is_measure mu -> is_regular_measure phi ->
  is_measure_density phi (partial_function_total (fun x=>(h x)%:E : extended_real_line R)) mu ->
  continuous h -> (forall x, 0<h x) ->
  covering_relation_fine_at (positive_finite_containing_relation phi) a ->
  partial_function_graph (measure_derivate mu phi (positive_finite_containing_relation phi))
    a (h a)%:E.
Proof.
move=> hPhi hMu hRegular hDensity hCont hPositive hFine.
pose V := positive_finite_containing_relation phi.
have hDomain : covering_relation_fine_at
    (fun x S=>V x S /\ partial_function_domain (measure_ratio_function mu phi) S) a.
  apply: (@covering_relation_fine_mono R X V _ a _ hFine)=> S hS.
  split; first exact hS.
  exists (mu S/phi S)%E; exact: measure_ratio_positive_finite_denominator hS.2.1 hS.2.2.
apply: (@covering_finite_limit_of_small_values R X V (measure_ratio_function mu phi) a (h a) hDomain).
move=> e he.
pose t := Num.min (e/2) (h a/2).
have hTwo : 0<(2 : R) by rewrite ltr0n.
have ht : 0<t by rewrite /t lt_min !divr_gt0 //; exact: hPositive.
have hte : t<=e/2 by rewrite /t ge_min lexx.
have hth : t<=h a/2 by rewrite /t ge_min lexx orbT.
have hLow0 : 0<h a-t by have := hPositive a; lra.
have hUp0 : 0<h a+t := addr_gt0 (hPositive a) ht.
have hteStrict : t<e by lra.
have hNb : nbhs (h a) [set y : real_line_metric R | `|h a-y|<t].
  apply: (metricType_numDomainType.nbhs_mdistP (h a) _).2.
  exists t=> // y hy; by rewrite -real_line_metric_distanceE.
have hPre := hCont a _ hNb.
have [d hd hControl] := (metricType_numDomainType.nbhs_mdistP a _).1 hPre.
exists d; split; first exact hd.
move=> S y hS hDiam hy.
have hNear x (hx : S x) : `|h a-h x|<t.
  have hD := @metric_diameter_upper R X S (extended_metric_diameter S)
    (extended_metric_diameter_specification S) a x hS.1 hx.
  have hSmall : mdist a x<d by move: (le_lt_trans hD hDiam); rewrite lte_fin.
  exact: hControl x hSmall.
have hLower : (((h a-t)%:E)*phi S<=mu S)%E.
  apply: (@nonnegative_density_set_lower_bound R X phi mu hPhi
    (fun x=>(h x)%:E) S (h a-t) hDensity).
  - move=> x; rewrite lee_fin; exact: ltW (hPositive x).
  - exact hLow0.
  - move=> x hx; rewrite lee_fin.
    have /andP [hl hu] : -t<h a-h x<t by rewrite -ltr_norml; exact: hNear x hx.
    lra.
have hUpper : (mu S<=((h a+t)%:E)*phi S)%E.
  apply: (@nonnegative_density_set_upper_bound R X phi mu hPhi
    (fun x=>(h x)%:E) S (h a+t) hRegular hDensity hUp0).
  move=> x hx; rewrite lee_fin.
  have /andP [hl hu] : -t<h a-h x<t by rewrite -ltr_norml; exact: hNear x hx.
  lra.
pose b := fine (phi S).
have hB : phi S=b%:E by rewrite /b (fineK hS.2.2).
have hb : 0<b by move: hS.2.1; rewrite hB lte_fin.
have hMuFinite : mu S \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hMu S)).
  apply: le_lt_trans hUpper _; rewrite hB -EFinM; exact: ltry.
pose q := fine (mu S).
have hQ : mu S=q%:E by rewrite /q (fineK hMuFinite).
have hValue := @measure_ratio_positive_finite_denominator R X mu phi S hS.2.1 hS.2.2.
have hY : y=(mu S/phi S)%E := partial_function_single_valued hy hValue.
rewrite hY hB hQ inver (gt_eqF hb) -EFinM !lte_fin.
have hL : h a-t<=q/b.
  rewrite ler_pdivlMr //; move: hLower; by rewrite hQ hB -EFinM lee_fin.
have hU : q/b<=h a+t.
  rewrite ler_pdivrMr //; move: hUpper; by rewrite hQ hB -EFinM lee_fin.
split; lra.
Qed.
