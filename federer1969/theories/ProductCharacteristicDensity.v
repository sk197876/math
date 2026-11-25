(** Federer (1969), 2.6.4, pp. 118–119: every characteristic function of a
    measurable finite-product-measure set belongs to the L1 closure of the
    tensor image. The proof uses finite rectangular approximations and the
    actual integral of the absolute error, retaining the book's total-domain
    convention after erratum p. 2, book p. 119 lines 3, 4, 6. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure MeasureSequencePrefixes
  ProductMeasure ProductRectangleMeasurability MeasureIntegralUP MeasureCharacteristicIntegral
  SummableRealFunctionUP CharacteristicFunctionUP CharacteristicFunctionSealed CharacteristicUnionArithmetic
  SetSequenceDisjointification ProductRectangleApproximation SummableTensorImage FiniteRectangleUnionImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [product_characteristic_lone_dense]: the
    characteristic-function closure assertion in Federer 2.6.4,
    pp. 118–119, with an explicit finite integral of the
    approximation error. No sigma-finiteness of either factor is assumed. *)
Theorem product_characteristic_lone_dense (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X*Y))
    (s : (X*Y) -> R) (e : R) :
  measure_measurable (product_measure ha hb) S -> (product_measure ha hb S < +oo)%E ->
  is_characteristic_function S s -> 0<e ->
  exists (h : (X*Y) -> R) (q : R), separated_summable_image ha hb h /\
    is_measure_integral (product_measure ha hb)
      (real_total_integrand (fun p => `|h p-s p|)) q%:E /\ q<e.
Proof.
move=> hS hfin hs he.
have [C [D [n [hCD herror]]]] := @product_finite_rectangle_approximation R X Y alpha beta ha hb S e hS hfin he.
pose U := set_sequence_prefix (fun k => C k `*` D k) n.
pose h := @CharacteristicFunction.value R (X*Y)%type U.
have hh : is_characteristic_function U h := @CharacteristicFunction.laws R (X*Y)%type U.
have hU : measure_measurable (product_measure ha hb) U.
  apply: (@measure_sequence_prefix_measurable R (Choice.clone (X*Y)%type _) _
    (product_measure_is_measure ha hb) (fun k => C k `*` D k) _ n)=> k.
  exact (@product_measure_rectangle_measurable R X Y alpha beta ha hb (C k) (D k) (hCD k).1 (hCD k).2.2.1).
pose E := (U `\` S) `|` (S `\` U).
have hE : measure_measurable (product_measure ha hb) E.
  apply: (@measure_measurable_union R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb)).
  - exact (@measure_measurable_difference R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb) U S hU hS).
  - exact (@measure_measurable_difference R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb) S U hS hU).
have hbnd : (product_measure ha hb E < e%:E)%E by rewrite /E setUC.
have hef : product_measure ha hb E \is a fin_num.
  rewrite ge0_fin_numE; last exact (@measure_nonnegative R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb) E).
  exact: lt_trans hbnd (ltry e).
exists h,(fine (product_measure ha hb E)); split.
- exact (@finite_rectangle_union_characteristic_image R X Y alpha beta ha hb C D n h hCD hh).
split.
- rewrite fineK //.
  exact (@measure_characteristic_integral R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb)
    E _ (characteristic_absolute_difference hh hs) hE).
- have hh' := hbnd; rewrite -(fineK hef) lte_fin in hh'; exact hh'.
Qed.
