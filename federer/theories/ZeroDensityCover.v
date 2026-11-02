(** Federer (1969), 2.9.12, pp. 158–159: densities and approximate limits of
    functions on partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureDerivationContext
  MeasureRestriction MeasureDerivates MeasureSetDensity CoveringRelationLimits
  CoveringFiniteLimitBounds CoveringLowerSublevel MetricDiameterUP MetricDiameter
  MeasureRatioComparison MeasureSplit CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [zero_density_cover_impossible]: supporting uniqueness
    argument in Federer 2.9.12, p. 158, last paragraph Two sets covering X
    cannot both have density zero at one point. A finite zero limit itself
    supplies a defined cell; no positivity of all Vitali-cell measures is
    assumed. *)
Lemma zero_density_cover_impossible (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A B : set X) x :
  is_measure_derivation_context phi V -> A `|` B=setT ->
  partial_function_graph (measure_set_density phi V A) x 0 ->
  partial_function_graph (measure_set_density phi V B) x 0 -> False.
Proof.
move=> hc hcover hA hB.
have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
pose e := ((2%:R : R)^-1)%R.
have he : (0<e)%R by rewrite /e invr_gt0 ltr0n.
have [a [ha hsa]] := @covering_finite_limit_small_values R X V
  (measure_ratio_function (measure_restrict phi A) phi) x 0 e hA he.
have [b [hb hsb]] := @covering_finite_limit_small_values R X V
  (measure_ratio_function (measure_restrict phi B) phi) x 0 e hB he.
pose d := (Num.min a b)%R.
have hd : (0<d)%R by rewrite /d lt_min ha hb.
have hlo : covering_lower_limit V (measure_ratio_function (measure_restrict phi A) phi) x<1.
  by rewrite hA.2.2 lte_fin ltr01.
have [S [y [hS [hdiam [hy _]]]]] := @covering_lower_limit_small_value R X V
  (measure_ratio_function (measure_restrict phi A) phi) x 1 d hlo hd.
have hbounded : metric_set_bounded S := lt_trans hdiam (ltry d).
have hfin : phi S \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm S)); exact: derivation_measure_bounded_finite hphi S hbounded.
have hnonzero : phi S != 0.
  apply/negP=> /eqP hz; exact: (@measure_ratio_zero_denominator R X (measure_restrict phi A) phi S hz (ex_intro _ y hy)).
have hpos : 0<phi S by rewrite lt_def hnonzero (measure_nonnegative hm).
have hfa : phi (A `&` S) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  apply: le_lt_trans (@measure_mono R X phi hm (A `&` S) S (fun z hz => hz.2)) _.
  exact: derivation_measure_bounded_finite hphi S hbounded.
have hfb : phi (B `&` S) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  apply: le_lt_trans (@measure_mono R X phi hm (B `&` S) S (fun z hz => hz.2)) _.
  exact: derivation_measure_bounded_finite hphi S hbounded.
have hda : extended_metric_diameter S<a%:E.
  apply: lt_le_trans hdiam _; by rewrite lee_fin /d ge_min lexx.
have hdb : extended_metric_diameter S<b%:E.
  apply: lt_le_trans hdiam _; by rewrite lee_fin /d ge_min lexx orbT.
have hya : y<e%:E by have := (hsa S y hS hda hy).2; rewrite add0r.
have hz := @measure_ratio_positive_finite_denominator R X (measure_restrict phi B) phi S hpos hfin.
have hzb : measure_restrict phi B S/phi S<e%:E.
  by have := (hsb S _ hS hdb hz).2; rewrite add0r.
have hla := @finite_measure_ratio_comparison R X (measure_restrict phi A) phi S e y hfa hfin hpos hy hya.
have hlb := @finite_measure_ratio_comparison R X (measure_restrict phi B) phi S e _ hfb hfin hpos hz hzb.
have hsub : S `<=` (A `&` S) `|` (B `&` S).
  move=> z hzS; have : (A `|` B) z by rewrite hcover.
  by case=> hzAB; [left|right]; split.
have hmass := @measure_binary_cover R X phi hm S (A `&` S) (B `&` S) hsub.
have hlt : phi (A `&` S)+phi (B `&` S)<e%:E*phi S+e%:E*phi S.
  apply: lteD => //; by rewrite /measure_restrict in hla hlb.
have heq : e%:E*phi S+e%:E*phi S=phi S.
  rewrite -(fineK hfin) -!EFinM -EFinD -mulrDl /e.
  have heunit : (e+e = 1)%R.
    have hs := splitr (1%R : R).
    rewrite !mul1r in hs; exact: esym hs.
  by rewrite heunit mul1r.
by have := le_lt_trans hmass hlt; rewrite heq ltxx.
Qed.
