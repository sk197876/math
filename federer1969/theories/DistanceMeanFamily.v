(** Federer (1969), 2.9.9, pp. 156–157: fixed-target distance functions in
    the Lebesgue-point proof. We retain Federer's exponent one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP
  MeasureBasic MeasurableFunctionUP MeasureSubsetIntegral MeasurableDistanceTo
  DistanceMeanValues MeasureMeanFunction MeasureDerivationContext CoveringFamilyUP
  CoveringRelationUP MetricDiameter BorelRegularMeasureUP CoveringLipschitzFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [distance_means_form_lipschitz_family]: supporting uniform
    family of local averages in Federer 2.9.9, p. 157 The common partial
    domain on small cells is precisely the positive-measure cells.
    Finiteness follows from boundedness and the original local hypothesis. *)
Theorem distance_means_form_lipschitz_family (R : realType) (X Y : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X Y) (base : Y) :
  is_measure_derivation_context phi V -> is_measure_measurable_function phi f ->
  (forall A, metric_set_bounded A -> measure_measurable phi A -> exists a : R,
    is_measure_subset_integral phi A (partial_distance_to f base) a%:E) ->
  is_covering_lipschitz_family V (fun y => measure_mean_function phi (partial_distance_to f y)) 1%R.
Proof.
move=> hc hf hlocal.
have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
have hcell x S : V x S -> extended_metric_diameter S<1%:E ->
    measure_measurable phi S /\ phi S \is a fin_num /\
    exists c : R, is_measure_subset_integral phi S (partial_distance_to f base) c%:E.
  move=> hS hd.
  have hSb : metric_set_bounded S := lt_trans hd (ltry _).
  have hB := @vitali_relation_borel R X phi V (derivation_context_vitali hc) S
    (ex_intro _ x (conj Logic.I hS)).
  have hSm := @borel_regular_borel_measurable R X phi hm (derivation_measure_borel_regular hphi) S hB.
  split=> //; split; last exact: hlocal S hSb hSm.
  rewrite (ge0_fin_numE (measure_nonnegative hm S)).
  exact: derivation_measure_bounded_finite hphi S hSb.
have hpositive S y : partial_function_domain (measure_mean_function phi (partial_distance_to f y)) S -> 0<phi S.
  move=> hy; rewrite lt_def (measure_nonnegative hm S) andbT.
  apply/negP=> /eqP hz; apply: (@measure_mean_zero_denominator R X phi (partial_distance_to f y) S hz); exact hy.
have hvalues x S y z : V x S -> extended_metric_diameter S<1%:E ->
    0<phi S -> exists a d : R,
    partial_function_graph (measure_mean_function phi (partial_distance_to f y)) S a%:E /\
    partial_function_graph (measure_mean_function phi (partial_distance_to f z)) S d%:E /\
    (`|a-d|<=mdist y z)%R.
  move=> hS hd hp; have [hSm [hSf hbase]] := hcell x S hS hd.
  have he : phi S=(fine (phi S))%:E by rewrite fineK.
  have hbp : (0<fine (phi S))%R by move: hp; rewrite he lte_fin.
  exact (@finite_distance_mean_values R X Y phi f S (fine (phi S)) base y z hm hf hSm he hbp hbase).
constructor.
- move=> x S hS hd y z hy.
  have [a [d [_ [hz _]]]] := hvalues x S y z hS hd (hpositive S y hy).
  by exists d%:E.
- move=> x S hS hd y v hv.
  have [a [d [hy _]]] := hvalues x S y y hS hd (hpositive S y (ex_intro _ v hv)).
  have he := partial_function_single_valued hv hy; by rewrite he fin_numE.
- move=> x S hS hd y z a b ha hb.
  have [c [d [hy [hz hcd]]]] := hvalues x S y z hS hd (hpositive S y (ex_intro _ a%:E ha)).
  have hea := partial_function_single_valued ha hy.
  have heb := partial_function_single_valued hb hz.
  have eac : a=c by apply/eqP; move: hea=> /eqP; rewrite eqe.
  have ebd : b=d by apply/eqP; move: heb=> /eqP; rewrite eqe.
  by rewrite eac ebd.
Qed.
