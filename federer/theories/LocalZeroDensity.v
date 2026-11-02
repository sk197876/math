(** Federer (1969), 2.9.13, p. 159: measurability and almost-everywhere
    approximate continuity. The erratum p. 3, book p. 159 line 19, corrects
    the order of the pair to (phi,V). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureRestriction MeasureDerivates
  MeasureDerivationContext MeasureSetDensity SetDensityRatios DerivationRatioDomain
  CoveringFamilyUP CoveringRelationUP CoveringRelationFineness CoveringRelationLimits
  CoveringFiniteLimitBounds CoveringLowerSublevel MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [zero_density_other_ratio_domain_fine]: supporting domain
    fineness for the local density comparison in Federer 2.9.13, p. 159 A
    finite zero density for B supplies arbitrarily small defined cells for
    the density ratio of any A. Null cells are not filled by assigning an
    artificial quotient. *)
Lemma zero_density_other_ratio_domain_fine (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A B : set X) x :
  is_derivation_measure phi ->
  partial_function_graph (measure_set_density phi V B) x 0 ->
  covering_relation_fine_at (fun x S => V x S /\
    partial_function_domain (measure_ratio_function (measure_restrict phi A) phi) S) x.
Proof.
move=> hphi hB.
have hlo : covering_lower_limit V (measure_ratio_function (measure_restrict phi B) phi) x<1.
  by rewrite hB.2.2 lte_fin ltr01.
apply: (covering_relation_fine_iff_small_diameter _ x).2=> e he.
have [S [y [hS [hd [hy _]]]]] := @covering_lower_limit_small_value R X V
  (measure_ratio_function (measure_restrict phi B) phi) x 1 e hlo he.
have hbounded : metric_set_bounded S := lt_trans hd (ltry e).
exists S; split=> //; split=> //.
exists (measure_restrict phi A S/phi S).
exact: bounded_density_ratio_common_domain hphi hbounded hy.
Qed.

(** Source for [local_zero_density_mono]: supporting local comparison of
    exceptional sets in Federer 2.9.13, p. 159 If A is contained in B near x
    and B has density zero at x, then A has density zero there. No
    measurability of A or B is needed. Small covering cells contain x and
    lie in the chosen open neighbourhood. *)
Theorem local_zero_density_mono (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A B U : set X) x :
  is_measure_derivation_context phi V -> open U -> U x ->
  (forall z, U z -> A z -> B z) ->
  partial_function_graph (measure_set_density phi V B) x 0 ->
  partial_function_graph (measure_set_density phi V A) x 0.
Proof.
move=> hc hU hxU hAB hB; have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
have hnb : nbhs x U by rewrite openE in hU; exact: hU x hxU.
have [r hr hUr] := (metricType_numDomainType.nbhs_mdistP x _).1 hnb.
apply: (@covering_finite_limit_of_small_values R X V
  (measure_ratio_function (measure_restrict phi A) phi) x 0).
- exact: zero_density_other_ratio_domain_fine hphi hB.
- move=> e he.
  have [b [hb hsmall]] := @covering_finite_limit_small_values R X V
    (measure_ratio_function (measure_restrict phi B) phi) x 0 e hB he.
  exists (Num.min b r); split; first by rewrite lt_min hb hr.
  move=> S y hS hd hy.
  have hdb : extended_metric_diameter S<b%:E.
    apply: lt_le_trans hd _; by rewrite lee_fin ge_min lexx.
  have hdr : extended_metric_diameter S<r%:E.
    apply: lt_le_trans hd _; by rewrite lee_fin ge_min lexx orbT.
  have hbounded : metric_set_bounded S := lt_trans hdr (ltry r).
  have hSU : S `<=` U.
    move=> z hz; apply: hUr.
    have hxS := @vitali_relation_covering R X phi V (derivation_context_vitali hc) x S hS.
    have hdist := metric_diameter_upper (extended_metric_diameter_specification S) hxS hz.
    by have := le_lt_trans hdist hdr; rewrite lte_fin.
  have hz := @bounded_density_ratio_common_domain R X phi B A S y hphi hbounded hy.
  have horder : y<=measure_restrict phi B S/phi S.
    apply: (@bounded_density_ratio_order R X phi A B S y _ hphi hbounded _ hy hz).
    by move=> z [hzA hzS]; split=> //; exact: hAB z (hSU z hzS) hzA.
  have hpos := @measure_ratio_nonnegative R X (measure_restrict phi A) phi S y
    (measure_restrict_is_measure hm A) hm hy.
  split.
  + rewrite sub0r; apply: lt_le_trans _ hpos; by rewrite lte_fin oppr_lt0.
  + have hlt := (hsmall S _ hS hdb hz).2.
    rewrite add0r in hlt; rewrite add0r; exact: le_lt_trans horder hlt.
Qed.
