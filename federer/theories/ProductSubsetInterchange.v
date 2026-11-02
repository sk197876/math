(** Federer (1969), 2.9.25, p. 169: interchange the iterated prefix integral
    by 2.6.2(4), p. 115. Summability, rather than a sigma-finiteness
    assumption on the factors, supplies this Fubini case. No relevant entry
    occurs in the local Federer erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  PartialZeroExtensionLaws PartialProductSections ProductRectangleRestriction
  MeasureUP MeasureBasic MeasureSplit MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence MeasureSubsetIntegral MeasureDensityNullSets
  ProductMeasure ProductRectangleMeasurability ParameterizedIntegral ParameterizedIntegralLaws
  SummableSubsetRestriction ProductSummableFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [product_subset_vertical_graph]: supporting
    section identity for the prefix integral in Federer
    2.9.25, p. 169, under the subset convention 2.4.10,
    p. 85. All first coordinates are retained. *)
Lemma product_subset_vertical_graph (X Y Z : Type) (zero : Z)
    (B : set Y) (f : partial_function (X*Y) Z) x y z :
  partial_function_graph (partial_product_vertical_section
    (partial_function_zero_extension zero (setT `*` B) f) x) y z <->
  partial_function_graph (partial_function_zero_extension zero B
    (partial_product_vertical_section f x)) y z.
Proof.
change (partial_function_graph (partial_function_zero_extension zero (setT `*` B) f) (x,y) z <->
  partial_function_graph (partial_function_zero_extension zero B (partial_product_vertical_section f x)) y z).
rewrite !partial_function_zero_extension_graph /=; split.
- move=> [[[_ hy] hf]|[hn hz]]; [by left|right; split=> // hy; apply: hn; by split].
- move=> [[hy hf]|[hn hz]]; [left; split=> //; by split|right; split=> //; by move=> [_ hy]; apply: hn].
Qed.

(** Source for [parameterized_integral_subset_horizontal_graph]:
    supporting inner-integral restriction in Federer 2.9.25,
    p. 169. On B the original section is retained; off B
    the section is total zero, whose actual integral is zero
    even when the first measure is infinite. *)
Lemma parameterized_integral_subset_horizontal_graph (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (ha : is_measure alpha) (B : set Y)
    (f : partial_function (X*Y) (extended_real_line R)) y z :
  partial_function_graph (parameterized_integral alpha (partial_product_horizontal_section
    (partial_function_zero_extension (0 : extended_real_line R) (setT `*` B) f))) y z <->
  partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) B
    (parameterized_integral alpha (partial_product_horizontal_section f))) y z.
Proof.
case: (pselect (B y))=> hy.
- rewrite (partial_function_zero_extension_on _ _ _ hy) !parameterized_integral_specification.
  split=> hi; apply: (@measure_integral_graph_equivalent R X alpha _ _ z _ hi)=> x w.
  + by rewrite (@rectangle_restriction_horizontal_on X Y (extended_real_line R)
      0 setT B f y hy x w) partial_zero_extension_whole_graph.
  + symmetry; by rewrite (@rectangle_restriction_horizontal_on X Y (extended_real_line R)
      0 setT B f y hy x w) partial_zero_extension_whole_graph.
- rewrite (partial_function_zero_extension_off _ _ _ hy) parameterized_integral_specification.
  have hzero : is_measure_integral alpha (partial_product_horizontal_section
      (partial_function_zero_extension (0 : extended_real_line R) (setT `*` B) f) y) 0%E.
    apply: (@measure_integral_graph_equivalent R X alpha _ _ 0%E _ (measure_extended_zero_integral ha))=> x w.
    rewrite (@rectangle_restriction_horizontal_off X Y (extended_real_line R)
      0 setT B f y hy x w).
    change (0%E=w <-> w=0%E); split=> ->; by [].
  split; first by move=> hi; exact: measure_integral_unique hi hzero.
  by move=> ->.
Qed.

(** Source for [product_summable_subset_interchange]: direct Fubini step in
    Federer 2.9.25, p. 169 A measurable restriction of a summable joint
    integrand remains summable. Both iterated integrals therefore exist with
    the same finite value, retaining exact domains for all inner integrals. *)
Theorem product_summable_subset_interchange (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : partial_function (X*Y) (extended_real_line R)) (B : set Y) (z : \bar R) :
  is_measure_summable (product_measure ha hb) f -> measure_measurable beta B ->
  is_measure_integral alpha (parameterized_integral beta (fun x =>
    partial_function_zero_extension (0 : extended_real_line R) B (partial_product_vertical_section f x))) z ->
  is_measure_subset_integral beta B
    (parameterized_integral alpha (partial_product_horizontal_section f)) z.
Proof.
move=> hf hB houter.
have hrect := @product_measure_rectangle_measurable R X Y alpha beta ha hb setT B
  (measure_measurable_whole ha) hB.
have [I hI] := @summable_measurable_zero_extension R (X*Y)%type (product_measure ha hb)
  (product_measure_is_measure ha hb) (setT `*` B) f hrect hf.
have [hV hH] := @product_summable_fubini R X Y alpha beta ha hb _ I hI.
have hV' : is_measure_integral alpha (parameterized_integral beta (fun x =>
    partial_function_zero_extension (0 : extended_real_line R) B (partial_product_vertical_section f x))) I%:E.
  apply: (@measure_integral_graph_equivalent R X alpha _ _ I%:E _ hV).
  apply: parameterized_integral_graph_equivalent=> x y w.
  exact: product_subset_vertical_graph.
have he := measure_integral_unique hV' houter.
rewrite -he; apply: (@measure_integral_graph_equivalent R Y beta _ _ I%:E _ hH).
exact (@parameterized_integral_subset_horizontal_graph R X Y alpha ha B f).
Qed.
