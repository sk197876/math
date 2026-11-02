(** Federer (1969), proof of 2.4.6, p. 84: finite sums of weighted
    characteristic functions have the expected integrals by 2.4.4(3)–(4) and
    2.4.5. The intermediate real-valued finite-sum law below is supporting
    infrastructure; nonnegative integral values ensure every sum is defined,
    without requiring finiteness. Source context: ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic
  PartialExtendedArithmetic ExtendedRealPartial MeasureUP MeasureStepConstants
  MeasureStepIntegralIdentification MeasureIntegralUP MeasureIntegralAddition MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_total_sum_embedding_graph]: supporting
    real-to-extended graph identity for finite simple sums in
    Federer 2.4.6, p. 84. Finite real values always add. *)
Lemma real_total_sum_embedding_graph (R : realType) (X : Type)
    (u v : X -> real_line_metric R) x y :
  partial_function_graph (partial_extended_function_add
    (partial_real_function_embed (partial_function_total u))
    (partial_real_function_embed (partial_function_total v))) x y <->
  partial_function_graph (partial_real_function_embed
    (partial_function_total (fun x => ((u x + v x)%R : real_line_metric R)))) x y.
Proof.
rewrite partial_extended_function_add_graph; split.
- move=> [a [b [[r [hr era]] [[s [hs esb]] hab]]]].
  have he : (u x + v x)%:E = y.
    move: hab; rewrite -era -esb -(hr : u x = r) -(hs : v x = s) /extended_add /=.
    by move=> [].
  exists (u x+v x)%R; by split.
- move=> [r [hr ery]]; exists (u x)%:E, (v x)%:E; split; first by exists (u x); split.
  split; first by exists (v x); split.
  by rewrite /extended_add /= -EFinD hr ery.
Qed.

(** Source for [measure_finite_real_sum_integral]: supporting
    finite additivity of the test functions' integrals in Federer
    2.4.6, p. 84, from 2.4.4(4). *)
Lemma measure_finite_real_sum_integral (R : realType) (X : choiceType) (I : eqType)
    (mu : set X -> \bar R) (hm : is_measure mu) (s : seq I)
    (u : I -> X -> real_line_metric R) (a : I -> \bar R) :
  (forall i, i \in s -> 0 <= a i) ->
  (forall i, i \in s -> is_measure_integral mu
    (partial_real_function_embed (partial_function_total (u i))) (a i)) ->
  is_measure_integral mu (partial_real_function_embed
    (partial_function_total (fun x => ((\sum_(i <- s) u i x)%R : real_line_metric R))))
    (\sum_(i <- s) a i).
Proof.
elim: s=> [|i s ih] hp hi.
- have he : (fun x : X => ((\sum_(i <- [::]) u i x)%R : real_line_metric R)) = (fun _ => 0%R).
    by apply: funext=> x; rewrite big_nil.
  rewrite he big_nil.
  have ha := @measure_step_constant_integral R X mu hm 0%R; rewrite mul0e in ha.
  exact (@measure_step_function_integral R X mu hm _ 0 (@measure_step_constant R X mu hm 0%R) ha).
- have hps j : j \in s -> 0 <= a j.
    move=> hj; apply: hp; by rewrite in_cons hj orbT.
  have his j : j \in s -> is_measure_integral mu
      (partial_real_function_embed (partial_function_total (u j))) (a j).
    move=> hj; apply: hi; by rewrite in_cons hj orbT.
  have hsum : 0 <= \sum_(j <- s) a j by rewrite big_seq; exact: sume_ge0.
  have hd : extended_add (a i) (\sum_(j <- s) a j) = Some (a i + \sum_(j <- s) a j).
    rewrite /extended_add; have hh := ge0_adde_def (hp i (mem_head i s)) hsum; by rewrite hh.
  have h := @measure_integral_add R X mu hm _ _ _ _ _ (hi i (mem_head i s)) (ih hps his) hd.
  have he : (fun x : X => ((\sum_(j <- i::s) u j x)%R : real_line_metric R)) =
      (fun x => (u i x + \sum_(j <- s) u j x)%R).
    by apply: funext=> x; rewrite big_cons.
  rewrite he big_cons.
  exact: measure_integral_graph_equivalent (real_total_sum_embedding_graph _ _) h.
Qed.
