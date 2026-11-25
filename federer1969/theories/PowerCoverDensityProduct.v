(** Federer (1969), 2.10.29, p. 195: local power-density bounds multiply
    under Cartesian products. This supporting argument uses closures of the
    two projected test sets, whose diameters do not increase. They are
    measurable for the Borel regular factor measures. Only one small
    coefficient is needed; the other is fixed at one. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealPower PowerCoverDensityUP PowerCoverDensityScalars
  MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel
  MetricDiameter MetricDiameterMaps MetricDiameterClosure MetricCartesianProductUP
  MetricCartesianRectangleBounds LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [paired_product_vanishing_power_density]: supporting
    product step for 2.10.29, p. 195.
    Nonexpanding projections suffice for the local
    bound; no continuity or expansion estimate
    for the pairing is needed here. *)
Theorem paired_product_vanishing_power_density (R : realType) (P Y Z : metricType R)
    (pair : Y -> Z -> P) (first : P -> Y) (second : P -> Z)
    (hp : is_metric_cartesian_product pair first second)
    (alpha : set Y -> \bar R) (beta : set Z -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (p q : R) :
  (0<=p)%R -> (0<=q)%R ->
  is_borel_regular_measure alpha -> is_borel_regular_measure beta ->
  is_vanishing_power_cover_density p alpha -> is_vanishing_power_cover_density q beta ->
  is_vanishing_power_cover_density (p+q)%R (paired_product_measure pair ha hb).
Proof.
move=> hp0 hq0 hra hrb hda hdb e he.
have [a [ha0 hlocalA]] := hda e he.
have [b [hb0 hlocalB]] := hdb 1%R ltr01.
exists (Order.min a b); split; first by rewrite lt_min ha0 hb0.
move=> S d hd hdc hdiam.
have /andP[hda' hdb'] : ((d<=a) && (d<=b))%R by move: hdc; rewrite le_min.
pose F := closure (first @` S).
pose G := closure (second @` S).
have hfirst x y : (mdist (first x) (first y)<=mdist x y)%R.
  have hh := (metric_product_first_nonexpanding hp).2 x y Logic.I Logic.I.
  by rewrite mul1r in hh.
have hsecond x y : (mdist (second x) (second y)<=mdist x y)%R.
  have hh := (metric_product_second_nonexpanding hp).2 x y Logic.I Logic.I.
  by rewrite mul1r in hh.
have hFdiam : extended_metric_diameter F<=d%:E.
  rewrite /F extended_metric_diameter_closure.
  exact (le_trans (extended_metric_diameter_nonexpanding hfirst S) hdiam).
have hGdiam : extended_metric_diameter G<=d%:E.
  rewrite /G extended_metric_diameter_closure.
  exact (le_trans (extended_metric_diameter_nonexpanding hsecond S) hdiam).
have hF : measure_measurable alpha F.
  apply: (borel_regular_borel_measurable ha hra); apply: closed_borel_set; exact: closed_closure.
have hG : measure_measurable beta G.
  apply: (borel_regular_borel_measurable hb hrb); apply: closed_borel_set; exact: closed_closure.
have hcover x : S x -> F (first x) /\ G (second x).
  move=> hx; split; apply: subset_closure; by exists x.
have hrect := @paired_product_rectangle_bound R P Y Z pair first second hp alpha beta ha hb S F G hF hG hcover.
have halpha := hlocalA F d hd hda' hFdiam.
have hbeta := hlocalB G d hd hdb' hGdiam.
rewrite mul1r in hbeta.
have hfactor : 0<=(e*real_power d p)%R%:E.
  rewrite lee_fin; exact: mulr_ge0 (ltW he) (real_power_nonnegative _ _).
have hprod := le_trans (lee_wpmul2r (measure_nonnegative hb G) halpha) (lee_wpmul2l hfactor hbeta).
apply: le_trans hrect _; apply: le_trans hprod _.
by rewrite -EFinM real_power_nonnegative_exponents_add // mulrA.
Qed.
