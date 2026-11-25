(** Federer (1969), 2.4.19, p. 91: pass finite Jensen inequalities to limits
    using continuity of the vector integral and relative continuity of F.
    These supporting topology lemmas keep F defined continuously only on C. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground MetricSubsetBackground
  PartialFunctionUP MeasureUP MeasureLpConvergence MeasureVectorIntegralUP MeasureVectorIntegralDifference
  ExtendedRealOrderTopology ExtendedRealOrderLimit RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_vector_integral_sequence_continuous]: continuity of
    the vector integral used in Federer 2.4.19, p. 91, from 2.4.12, pp.
    87–88 *)
Lemma measure_vector_integral_sequence_continuous (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hN))
    (y : nat -> real_norm_metric_space hN) (z : real_norm_metric_space hN) :
  (forall n, is_measure_vector_integral mu (f n) (y n)) ->
  is_measure_vector_integral mu g z -> converges_in_lp_norm mu N 1%R f g -> y @ \oo --> z.
Proof.
move=> hi hg hl U hU.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP z U) hU.
have [K hK] := hl e he; exists K; first exact Logic.I.
move=> n hn; apply: hb; change ((mdist z (y n) < e)%R); rewrite metric_sym.
change ((N (y n-z) < e)%R).
have hbound := @measure_vector_integral_distance_bound R X V N hN mu hm (f n) g (y n) z (hi n) hg.
have hh := le_lt_trans hbound (hK n hn); by move: hh; rewrite lte_fin.
Qed.

(** Source for [relative_continuous_sequence_limit]: supporting use of
    continuity only on C in Federer 2.4.19, p. 91 *)
Lemma relative_continuous_sequence_limit (R : realType) (Y : metricType R) (Z : topologicalType)
    (C : set Y) (F : Y -> Z) (u : nat -> Y) (z : Y) :
  continuous (fun y : metric_subset C => F (val y)) ->
  (forall n, C (u n)) -> C z -> u @ \oo --> z -> (fun n => F (u n)) @ \oo --> F z.
Proof.
move=> hF hu hz hl B hB.
pose zz : metric_subset C := @exist Y (fun y => y \in C) z (mem_set hz).
have hn := hF zz B hB.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP zz _) hn.
have hball : nbhs z [set y | (mdist z y < e)%R].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP z _)); by exists e.
have [K _ hK] := hl _ hball; exists K; first exact Logic.I.
move=> n hKn.
pose yy : metric_subset C := @exist Y (fun y => y \in C) (u n) (mem_set (hu n)).
exact: (@hb yy (hK n hKn)).
Qed.

(** Source for [real_metric_extended_order_limit]: supporting conversion of
    the real limits in Federer 2.4.19, p. 91, to the order-neighborhood
    limits used by the integral theorems *)
Lemma real_metric_extended_order_limit (R : realType) (u : nat -> real_line_metric R) (a : real_line_metric R) :
  u @ \oo --> a -> extended_order_limit (fun n => (u n)%:E) a%:E.
Proof.
move=> hl; apply: real_error_extended_order_limit=> e he.
have hball : nbhs a [set y : real_line_metric R | (mdist a y < e)%R].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP a _)); by exists e.
have [K _ hK] := hl _ hball; exists K=> n hn.
have hh := hK n hn; change (is_true (`|a-u n| < e)%R) in hh; by rewrite distrC in hh.
Qed.

(** Source for [extended_order_limits_comparison]: passage of inequalities
    to limits in Federer 2.4.19, p. 91 The right-hand limit may be infinite
    in the final truncation argument. *)
Lemma extended_order_limits_comparison (R : realType) (u v : nat -> \bar R) (a b : \bar R) :
  extended_order_limit u a -> extended_order_limit v b ->
  (forall n, u n <= v n) -> a <= b.
Proof.
move=> hu hv hle; rewrite leNgt; apply/negP=> hba.
have [q [hbq hqa]] := @extended_rationals_order_dense R b a hba.
have [N hN] := hu.1 _ hqa; have [M hM] := hv.2 _ hbq.
pose k := maxn N M.
have hnk : (N <= k)%N := leq_maxl N M.
have hmk : (M <= k)%N := leq_maxr N M.
have hh := lt_trans (hN k hnk) (le_lt_trans (hle k) (hM k hmk)).
by move: hh; rewrite ltxx.
Qed.
