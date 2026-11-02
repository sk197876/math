(** Federer (1969), 2.4.14, p. 88: equality in the integrated
    arithmetic-geometric comparison. The supporting lemma below applies to
    ordered finite-valued integrands, by integrating their nonnegative
    difference. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP PartialFunctionBasic
  PartialExtendedArithmetic PartialExtendedOrderLoci DominatedErrorGraphs
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralDifference MeasureNonnegativeZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_integral_order_equality]: supporting equality test
    in Federer 2.4.14, p. 88 Ordered real-valued integrands with the same
    finite integral agree almost everywhere. The finite graph witnesses
    explicitly exclude undefined infinity differences. *)
Lemma measure_integral_order_equality (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) (c : R) :
  is_measure_integral mu f c%:E -> is_measure_integral mu g c%:E ->
  measure_almost_everywhere mu [set x | exists a b : R,
    partial_function_graph f x a%:E /\ partial_function_graph g x b%:E /\ (a <= b)%R] ->
  measure_almost_equal mu f g.
Proof.
move=> hf hg horder.
have hi := @measure_integral_finite_difference R X mu hm g f c c hg hf.
rewrite subrr in hi.
have hgraph x (a b : R) : partial_function_graph f x a%:E -> partial_function_graph g x b%:E ->
    partial_function_graph (partial_extended_function_subtract g f) x (b-a)%:E.
  move=> ha hb; apply/partial_extended_function_add_graph.
  exists b%:E,(-a)%:E; split=> //; split.
  - exists a%:E; split=> //; by [].
  - by rewrite /extended_add /=.
have hpos : measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_extended_function_subtract g f)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ horder).
  move=> x [a [b [ha [hb hab]]]]; exists (b-a)%:E; split; first exact (hgraph x a b ha hb).
  by rewrite lee_fin subr_ge0.
have he := @nonnegative_integral_zero_almost_equal R X mu hm _ hi hpos.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ horder he)).
move=> x [[a [b [ha [hb hab]]]] [z [hz hz0]]].
have hdiff := hgraph x a b ha hb.
have hdiff0 : (b-a)%:E = (0 : \bar R).
  rewrite (partial_function_single_valued hdiff hz); exact: esym hz0.
have hsub : (b-a = 0)%R := EFin_inj hdiff0.
have heab : b=a by move/eqP: hsub; rewrite subr_eq0=> /eqP.
exists a%:E; split=> //; by rewrite -heab.
Qed.
