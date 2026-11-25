(** Federer (1969), 2.9.13, p. 159: measurability and almost-everywhere
    approximate continuity. The erratum p. 3, book p. 159 line 19, corrects
    the order of the pair to (phi,V). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureRestriction
  MeasureDerivates MeasureDerivationContext CoveringFamilyUP DerivationRatioDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_density_ratio_denominator]: supporting cell
    arithmetic in Federer 2.9.13, p. 159. A defined restricted-measure ratio
    on a bounded cell has a positive finite denominator in class M. This is
    infrastructure for the local density comparison. *)
Lemma bounded_density_ratio_denominator (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (A S : set X) y :
  is_derivation_measure phi -> metric_set_bounded S ->
  partial_function_graph (measure_ratio_function (measure_restrict phi A) phi) S y ->
  0<phi S /\ phi S \is a fin_num.
Proof.
move=> hphi hS hy; have hm := derivation_measure_law hphi.
have hn : phi S != 0.
  apply/negP=> /eqP hz.
  exact: (@measure_ratio_zero_denominator R X (measure_restrict phi A) phi S hz (ex_intro _ y hy)).
split; first by rewrite lt_def hn (measure_nonnegative hm).
rewrite (ge0_fin_numE (measure_nonnegative hm _)).
exact: derivation_measure_bounded_finite hphi S hS.
Qed.

(** Source for [bounded_density_ratio_common_domain]: supporting common
    ratio domains for the zero-density comparison in Federer 2.9.13, p. 159
    On a bounded cell a defined ratio for B supplies a defined ratio for
    every A, including nonmeasurable A. *)
Lemma bounded_density_ratio_common_domain (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (A B S : set X) y :
  is_derivation_measure phi -> metric_set_bounded S ->
  partial_function_graph (measure_ratio_function (measure_restrict phi B) phi) S y ->
  partial_function_graph (measure_ratio_function (measure_restrict phi A) phi) S
    (measure_restrict phi A S/phi S).
Proof.
move=> hphi hS hy; have [hp hf] := bounded_density_ratio_denominator hphi hS hy.
exact: measure_ratio_positive_finite_denominator hp hf.
Qed.

(** Source for [bounded_density_ratio_order]: supporting ratio monotonicity
    on bounded cells in Federer 2.9.13, p. 159 Only the intersections with
    the current cell must be ordered. Both values are actual partial ratios;
    the denominator is positive and finite. *)
Lemma bounded_density_ratio_order (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (A B S : set X) y z :
  is_derivation_measure phi -> metric_set_bounded S -> A `&` S `<=` B `&` S ->
  partial_function_graph (measure_ratio_function (measure_restrict phi A) phi) S y ->
  partial_function_graph (measure_ratio_function (measure_restrict phi B) phi) S z -> y<=z.
Proof.
move=> hphi hS hsub hy hz; have hm := derivation_measure_law hphi.
have [hp hf] := bounded_density_ratio_denominator hphi hS hy.
have hya := @measure_ratio_positive_finite_denominator R X (measure_restrict phi A) phi S hp hf.
have hzb := @measure_ratio_positive_finite_denominator R X (measure_restrict phi B) phi S hp hf.
have hey := partial_function_single_valued hy hya.
have hez := partial_function_single_valued hz hzb.
rewrite hey hez; apply: lee_wpmul2r; first by rewrite inve_ge0; exact: ltW hp.
exact: (@measure_mono R X phi hm (A `&` S) (B `&` S) hsub).
Qed.
