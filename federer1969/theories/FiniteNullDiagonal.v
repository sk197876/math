(** We isolate its measure-theoretic argument on a finite measurable
    rectangle: the vertical sections are empty or null singletons. This
    supports the local correction to Federer 2.6.5, p. 119, using 2.6.2(3),
    p. 115. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence PartialFunctionBasic SummableRealFunctionUP
  LatticeL1ApproximationLaws CountablyMeasurableBasic ProductMeasure ProductRectangleValue
  ProductSetFubini ProductSections ProductAssociativityObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restricted_diagonal_vertical]: Supporting local correction
    to Federer 2.6.5, p. 119. *)
Lemma restricted_diagonal_vertical (X : Type) (A : set X) (x : X) :
  product_vertical_section (restricted_diagonal A) x =
    if `[< A x >] then [set x] else set0.
Proof.
rewrite /product_vertical_section /restricted_diagonal /=.
case: ifP=> /asboolP hx; apply/seteqP; split=> y /=.
- by move=> [_ hxy].
- by move=> hxy; split.
- by move=> [h _]; exfalso; exact: hx h.
- by [].
Qed.

(** Source for [finite_measurable_diagonal_null]: Supporting Federer 2.6.5,
    p. 119.Only the second measure must have null singletons on A. *)
Theorem finite_measurable_diagonal_null (R : realType) (X : choiceType)
    (alpha beta : set X -> \bar R) (ha : is_measure alpha) (hb : is_measure beta)
    (A : set X) :
  measure_measurable alpha A -> measure_measurable beta A ->
  alpha A < +oo -> beta A < +oo ->
  (forall x, A x -> beta [set x] = 0) ->
  measure_measurable (product_measure ha hb) (restricted_diagonal A) ->
  product_measure ha hb (restricted_diagonal A) = 0.
Proof.
move=> hAa hAb hAf hBf hz hD.
have haF : alpha A \is a fin_num by rewrite ge0_fin_numE //; exact (measure_nonnegative ha _).
have hbF : beta A \is a fin_num by rewrite ge0_fin_numE //; exact (measure_nonnegative hb _).
have hsub : restricted_diagonal A `<=` A `*` A.
  move=> [x y] [hx hxy]; have he : x = y := hxy; subst y; by split.
have hbound := measure_mono (product_measure_is_measure ha hb) hsub.
rewrite (product_measure_rectangle_value ha hb hAa hAb) in hbound.
have hfin : product_measure ha hb (restricted_diagonal A) < +oo.
  apply: le_lt_trans hbound _.
  by rewrite -(fineK haF) -(fineK hbF) -EFinM ltry.
have hC := finite_measurable_set_countably_measurable hD hfin.
have [_ [_ [hI _]]] := @product_set_fubini R X X alpha beta ha hb (restricted_diagonal A) hC.
have hs : (fun x => beta (product_vertical_section (restricted_diagonal A) x))=
    (fun _ : X => (0 : \bar R)).
  apply: funext=> x; rewrite restricted_diagonal_vertical; case: ifP=> /asboolP hx.
  - exact: hz hx.
  - exact: measure_empty hb.
rewrite hs in hI.
have hzero : is_measure_integral alpha (partial_function_total (fun _ : X => (0 : \bar R))) 0.
  apply: (@measure_integral_graph_equivalent R X alpha
    (real_total_integrand (fun _ : X => (0%R : R))) _ 0).
  - by move=> x y; rewrite real_total_integrand_graph.
  - exact: real_total_zero_integral ha.
exact: measure_integral_unique hI hzero.
Qed.
