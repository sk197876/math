(** Recombining the two finite part means in Federer (1969), 2.9.8, p. 156.
    Here epsilon estimates prove its finite difference case directly.
    Outside the fine-null-cell fibers, every sufficiently small Vitali cell
    has positive finite reference mass and finite part integrals. This
    establishes domain fineness before applying the finite limit criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureBasic
  MeasurableFunctionUP MeasureDerivationContext CoveringFamilyUP CoveringRelationUP
  CoveringRelationFineness CoveringRelationLimits MetricDiameter BorelRegularMeasureUP
  DerivationRatioDomain MeasureMeanFunction LocalAbsoluteIntegrability FiniteMeanPartValues
  PartialFunctionIntegralParts MeasureUpperIntegralPositivePart CoveringFiniteLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [signed_mean_limit_from_parts]: supporting signed limit
    calculation in Federer 2.9.8, p. 156 Finite limits of the two part means
    give their difference as the signed mean limit. The null-fiber exception
    and local absolute integrability justify every denominator and the fine
    common domain. *)
Lemma signed_mean_limit_from_parts (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (extended_real_line R)) x (p n : R) :
  is_measure_derivation_context phi V -> is_measure_measurable_function phi f ->
  is_locally_absolutely_integrable phi f ->
  ~ covering_relation_fine_at (fun x S => V x S /\ phi S=0) x ->
  partial_function_graph (covering_relation_limit V
    (measure_mean_function phi (partial_extended_function_positive_part f))) x p%:E ->
  partial_function_graph (covering_relation_limit V
    (measure_mean_function phi (partial_extended_function_negative_part f))) x n%:E ->
  partial_function_graph (covering_relation_limit V (measure_mean_function phi f)) x (p-n)%R%:E.
Proof.
move=> hc hf hlocal hnP hLp hLn.
have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
have hv := derivation_context_vitali hc.
have [d [hd hnz]] := @nonfine_null_fiber_positive_scale R X phi V x hnP.
pose cap := (Num.min d 1)%R.
have hcap : (0<cap)%R by rewrite /cap lt_min hd ltr01.
have hcapd : (cap<=d)%R by rewrite /cap ge_min lexx.
have hcap1 : (cap<=1)%R by rewrite /cap ge_min lexx orbT.
have hcell S : V x S -> extended_metric_diameter S<cap%:E -> exists a b : R,
    partial_function_graph (measure_mean_function phi (partial_extended_function_positive_part f)) S a%:E /\
    partial_function_graph (measure_mean_function phi (partial_extended_function_negative_part f)) S b%:E /\
    partial_function_graph (measure_mean_function phi f) S (a-b)%R%:E.
  move=> hS hdiam.
  have hSd : extended_metric_diameter S<d%:E.
    apply: lt_le_trans hdiam _; by rewrite lee_fin.
  have hS1 : extended_metric_diameter S<1.
    apply: lt_le_trans hdiam _; by rewrite lee_fin.
  have hSb : metric_set_bounded S := lt_trans hS1 (@ltry R 1%R).
  have hSborel := @vitali_relation_borel R X phi V hv S (ex_intro _ x (conj Logic.I hS)).
  have hSm := @borel_regular_borel_measurable R X phi hm (derivation_measure_borel_regular hphi) S hSborel.
  have hSfin : phi S \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm S)); exact: derivation_measure_bounded_finite hphi S hSb.
  have hSpos : 0<phi S by rewrite lt_def (hnz S hS hSd) (measure_nonnegative hm S).
  exact (@finite_measure_mean_part_values R X phi f S hm hf hlocal hSb hSm hSpos hSfin).
have hdf : covering_relation_fine_at (fun x S => V x S /\
    partial_function_domain (measure_mean_function phi f) S) x.
  apply: (covering_relation_fine_iff_small_diameter _ x).2=> e he.
  have ht : (0<Num.min e cap)%R by rewrite lt_min he hcap.
  have [S [hS hdiam]] := (covering_relation_fine_iff_small_diameter V x).1 (vitali_relation_fine hv x) _ ht.
  have hScap : extended_metric_diameter S<cap%:E.
    apply: lt_le_trans hdiam _; by rewrite lee_fin ge_min lexx orbT.
  have [a [b [_ [_ hF]]]] := hcell S hS hScap.
  exists S; split.
  - split=> //; by exists (a-b)%R%:E.
  - apply: lt_le_trans hdiam _; by rewrite lee_fin ge_min lexx.
apply: (@covering_finite_limit_of_small_values R X V (measure_mean_function phi f) x (p-n)%R hdf)=> e he.
have he2 : (0<e/2)%R by rewrite divr_gt0 // ltr0n.
have [a [ha hpa]] := @covering_finite_limit_small_values R X V
  (measure_mean_function phi (partial_extended_function_positive_part f)) x p (e/2)%R hLp he2.
have [b [hb hnb]] := @covering_finite_limit_small_values R X V
  (measure_mean_function phi (partial_extended_function_negative_part f)) x n (e/2)%R hLn he2.
pose t := (Num.min cap (Num.min a b))%R.
have habpos : (0<Num.min a b)%R by rewrite lt_min ha hb.
have ht : (0<t)%R by rewrite /t lt_min hcap habpos.
exists t; split=> // S y hS hdiam hy.
have htc : (t<=cap)%R by rewrite /t ge_min lexx.
have hti : (t<=Num.min a b)%R by rewrite /t ge_min lexx orbT.
have hta : (t<=a)%R by apply: le_trans hti _; rewrite ge_min lexx.
have htb : (t<=b)%R by apply: le_trans hti _; rewrite ge_min lexx orbT.
have hScap : extended_metric_diameter S<cap%:E.
  apply: lt_le_trans hdiam _; by rewrite lee_fin.
have hSa : extended_metric_diameter S<a%:E.
  apply: lt_le_trans hdiam _; by rewrite lee_fin.
have hSb : extended_metric_diameter S<b%:E.
  apply: lt_le_trans hdiam _; by rewrite lee_fin.
have [u [v [hu [hv' hF]]]] := hcell S hS hScap.
have hpband := hpa S u%:E hS hSa hu.
have hnband := hnb S v%:E hS hSb hv'.
have hpl : (p-e/2<u)%R by move: hpband.1; rewrite lte_fin.
have hpu : (u<p+e/2)%R by move: hpband.2; rewrite lte_fin.
have hnl : (n-e/2<v)%R by move: hnband.1; rewrite lte_fin.
have hnu : (v<n+e/2)%R by move: hnband.2; rewrite lte_fin.
have hlo := ltrB hpl hnu.
have hhi := ltrB hpu hnl.
have elo : ((p-e/2)-(n+e/2)=(p-n)-(e/2+e/2))%R by ring.
have ehi : ((p+e/2)-(n-e/2)=(p-n)+(e/2+e/2))%R by ring.
rewrite elo -splitr in hlo; rewrite ehi -splitr in hhi.
have hyeq := partial_function_single_valued hy hF.
rewrite hyeq !lte_fin; by split.
Qed.
