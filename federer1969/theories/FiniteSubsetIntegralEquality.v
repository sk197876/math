(** The uniqueness inference in Federer (1969), 2.9.8, p. 156: equality of
    the subset integrals identifies f with the derivate almost everywhere.
    The supporting finite ordered-set step below uses the project's proved
    equality test for ordered finite integrals (supporting 2.4.14, p. 88),
    together with the subset convention 2.4.10, p. 85. Partial domains and
    finite-value witnesses are retained, so no undefined difference of
    infinities is formed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralOrderEquality MeasureSummableFiniteValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [equal_finite_subset_integrals_ordered]: supporting
    uniqueness on an ordered test set for Federer 2.9.8, p. 156 The common
    subset integral is finite, and both graph values exist on the ordered
    set. Equality holds almost everywhere on that set, without any arbitrary
    extension. *)
Lemma equal_finite_subset_integrals_ordered (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (f g : partial_function X (extended_real_line R)) A (c : R) :
  is_measure phi -> is_measure_subset_integral phi A f c%:E ->
  is_measure_subset_integral phi A g c%:E ->
  (forall x, A x -> partial_extended_le_locus f g x) ->
  measure_almost_everywhere_on phi A (partial_function_agreement f g).
Proof.
move=> hm hif hig horder.
pose F := partial_function_zero_extension (0 : extended_real_line R) A f.
pose G := partial_function_zero_extension (0 : extended_real_line R) A g.
have hfs : is_measure_summable phi F by exists c.
have hgs : is_measure_summable phi G by exists c.
have hFfin := @measure_summable_finite_almost R X phi hm F hfs.
have hGfin := @measure_summable_finite_almost R X phi hm G hgs.
have hcommon := @measure_almost_everywhere_and R X phi hm _ _ hFfin hGfin.
have hfiniteorder : measure_almost_everywhere phi [set x | exists a b : R,
    partial_function_graph F x a%:E /\ partial_function_graph G x b%:E /\ (a<=b)%R].
  apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ hcommon)=> x [[y [hy hyfin]] [z [hz hzfin]]].
  have hyR : partial_function_graph F x (fine y)%:E by rewrite fineK.
  have hzR : partial_function_graph G x (fine z)%:E by rewrite fineK.
  exists (fine y),(fine z); split=> //; split=> //.
  have hyz : y<=z.
    case: (pselect (A x))=> hx.
    - have hfy := (@partial_function_zero_extension_on X (extended_real_line R) (0 : extended_real_line R) A f x y hx).1 hy.
      have hgz := (@partial_function_zero_extension_on X (extended_real_line R) (0 : extended_real_line R) A g x z hx).1 hz.
      have [a [b [ha [hb hab]]]] := horder x hx.
      have ea := partial_function_single_valued ha hfy.
      have eb := partial_function_single_valued hb hgz.
      by rewrite -ea -eb.
    - have ey := (@partial_function_zero_extension_off X (extended_real_line R) (0 : extended_real_line R) A f x y hx).1 hy.
      have ez := (@partial_function_zero_extension_off X (extended_real_line R) (0 : extended_real_line R) A g x z hx).1 hz.
      by rewrite ey ez.
  by move: hyz; rewrite -(fineK hyfin) -(fineK hzfin) lee_fin.
have heq := @measure_integral_order_equality R X phi hm F G c hif hig hfiniteorder.
apply: (@measure_null_subset R X phi hm _ (~` partial_function_agreement F G)) heq.
move=> x [hx hn] [y [hy hz]]; apply: hn; exists y; split.
- exact: (@partial_function_zero_extension_on X (extended_real_line R) (0 : extended_real_line R) A f x y hx).1 hy.
- exact: (@partial_function_zero_extension_on X (extended_real_line R) (0 : extended_real_line R) A g x y hx).1 hz.
Qed.
