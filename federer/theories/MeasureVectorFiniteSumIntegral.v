(** Federer (1969), 2.4.12, pp. 87–88: finite-image functions lie in the
    subspace on which the vector integral exists. This supporting finite-sum
    law spells out that inference. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormedArithmetic
  MeasureUP MeasureAlmostBasic MeasureVectorIntegralUP MeasureVectorIntegralZero
  MeasureVectorIntegralAddition MeasureVectorIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_vector_total_finite_sum_integral]: supporting
    integration of finite sums of elementary functions in Federer 2.4.12,
    pp. 87–88 An empty index list gives the zero integral; repetitions are
    permitted. *)
Lemma measure_vector_total_finite_sum_integral (R : realType) (X : choiceType) (I : eqType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (s : seq I)
    (u : I -> X -> real_norm_metric_space hN) (y : I -> V) :
  (forall i, i \in s -> is_measure_vector_integral mu (partial_function_total (u i)) (y i)) ->
  is_measure_vector_integral mu (partial_function_total (fun x => (\sum_(i <- s) u i x)%R))
    (\sum_(i <- s) y i)%R.
Proof.
elim: s=> [|i s ih] hi.
- have he : (fun x => (\sum_(i <- [::]) u i x)%R) = (fun _ : X => (0%R : real_norm_metric_space hN)).
    by apply: funext=> x; rewrite big_nil.
  rewrite he big_nil; exact (@measure_vector_integral_zero R X V N hN mu hm).
- have his j : j \in s -> is_measure_vector_integral mu (partial_function_total (u j)) (y j).
    move=> hj; apply: hi; by rewrite in_cons hj orbT.
  have hj := ih his; have hii := hi i (mem_head i s).
  have hadd := @measure_vector_integral_add R X V N hN mu hm _ _ _ _ hii hj.
  rewrite big_cons.
  apply: (@measure_vector_integral_almost_equal R X V N hN mu hm _ _ _ hadd).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists (u i x+\sum_(j <- s) u j x)%R; split.
  + apply/partial_vector_add_graph; exists (u i x),(\sum_(j <- s) u j x)%R; by split=> //; split.
  + change ((\sum_(j <- i::s) u j x)%R=(u i x+\sum_(j <- s) u j x)%R).
    by rewrite big_cons.
Qed.
