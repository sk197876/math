(** Federer (1969), 2.4.8, p. 84: the finite case of interchanging a
    nonnegative sum and integration, by repeated application of 2.4.4(4).
    This supporting finite case retains extended values and the exact common
    domain. Source context: PartialNumericalSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP
  PartialFunctionBasic PartialExtendedArithmetic MeasureUP MeasureStepConstants MeasureStepIntegralIdentification
  MeasureIntegralUP MeasureIntegralAddition MeasureIntegralGraphEquivalence
  PartialNumericalSumUP PartialNumericalSum PartialNonnegativeSumLaws PartialNumericalSumInsert.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_finite_nonnegative_sum_integral]: finite
    index case supporting Federer 2.4.8, p. 84;
    empty sums have integral zero even if mu(X) is infinite. *)
Lemma measure_finite_nonnegative_sum_integral (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (C : {fset J})
    (f : J -> partial_function X (extended_real_line R)) (a : J -> \bar R) :
  (forall j, j \in C -> forall x y, partial_function_graph (f j) x y -> 0 <= y) ->
  (forall j, j \in C -> 0 <= a j) ->
  (forall j, j \in C -> is_measure_integral mu (f j) (a j)) ->
  is_measure_integral mu (partial_function_numerical_sum [set j | j \in C] f) (\sum_(j <- C) a j).
Proof.
elim/fset1U_rect: C=> [|i C hi ih] hp ha hf.
- have he : [set j : J | j \in fset0] = set0.
    apply/seteqP; split=> j; last by case.
    change ((j \in (fset0 : {fset J})) -> False).
    by rewrite in_fset0.
  rewrite he big_seq_fset0.
  have h0 := @measure_step_constant_integral R X mu hm 0%R; rewrite mul0e in h0.
  have hi0 := @measure_step_function_integral R X mu hm _ 0 (@measure_step_constant R X mu hm 0%R) h0.
  apply: (@measure_integral_graph_equivalent R X mu _ _ 0 _ hi0)=> x z.
  rewrite (@partial_numerical_sum_empty_graph R X J f _ (partial_function_numerical_sum_laws set0 f) x z).
  split.
  + move=> [r [hr erz]]; by rewrite -erz -(hr : 0%R=r).
  + move=> ->; exists 0%R; by split.
- have hC j : j \in C -> j \in (i |` C)%fset by move=> hj; rewrite in_fset1U hj orbT.
  have hii : i \in (i |` C)%fset by rewrite in_fset1U eqxx.
  have hpC j : j \in C -> forall x y, partial_function_graph (f j) x y -> 0 <= y.
    move=> hj; exact: hp j (hC j hj).
  have haC j : j \in C -> 0 <= a j by move=> hj; exact: ha j (hC j hj).
  have hfC j : j \in C -> is_measure_integral mu (f j) (a j).
    move=> hj; exact: hf j (hC j hj).
  have hsum : 0 <= \sum_(j <- C) a j by rewrite big_seq; exact: sume_ge0.
  have hadd : extended_add (a i) (\sum_(j <- C) a j) = Some (a i+\sum_(j <- C) a j).
    by rewrite /extended_add (ge0_adde_def (ha i hii) hsum).
  have h := @measure_integral_add R X mu hm _ _ _ _ _ (hf i hii) (ih hpC haC hfC) hadd.
  rewrite big_fsetU1 //; apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ h)=> x z.
  symmetry; exact (@partial_nonnegative_sum_insert_graph R X J C i f hi hp x z).
Qed.
