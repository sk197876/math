(** Federer (1969), 2.4.12, p. 87: finite-image density at p=infinity after
    the erratum p. 2, book p. 87 line 18, restricts this case to
    finite-dimensional targets. The existing Chapter 1 proof gives
    compactness in an auxiliary inner-product metric; this adapter transfers
    it to the supplied norm's own metric. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric LinearBasis InnerProductUP InnerNorm InnerMetric
  FiniteBasisInnerWitness FiniteNormUpperBound FiniteNormCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_to_given_norm_continuous]: supporting topology
    transfer for the compact ball used in Federer 2.4.12, p. 87 The supplied
    upper comparison makes identity continuous, including a zero comparison
    constant. *)
Lemma inner_to_given_norm_continuous (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (N : V -> R) (hN : is_real_norm N) (C : R) :
  0 <= C -> (forall x, N x <= C*inner_norm hB x) ->
  continuous (fun x : inner_metric_space hB => (x : real_norm_metric_space hN)).
Proof.
move=> hC hbound x U hU.
have [epsilon he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (x : real_norm_metric_space hN) U) hU.
have hC1 : 0 < C+1 by rewrite addrC ltr_pwDl.
have hdelta : 0 < epsilon/(C+1) by rewrite divr_gt0.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)).
exists (epsilon/(C+1))=> // y hy; apply: hball.
change (is_true (N (x-y) < epsilon)).
apply: le_lt_trans (hbound (x-y)) _.
have hCC : C <= C+1 by rewrite lerDl ler01.
apply: le_lt_trans (ler_wpM2r (inner_norm_nonnegative hB (x-y)) hCC) _.
rewrite mulrC -(@ltr_pdivlMr R (C+1) (inner_norm hB (x-y)) epsilon hC1).
exact hy.
Qed.

(** Source for [finite_norm_metric_ball_compact]: supporting compact ball
    assertion for the corrected infinity-endpoint density in Federer 2.4.12,
    p. 87 A finite basis suffices for any supplied norm; zero dimension and
    empty balls are included. The auxiliary inner product is only a witness. *)
Theorem finite_norm_metric_ball_compact (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) n (e : 'I_n -> V) :
  is_basis e -> forall r : R, compact [set x : real_norm_metric_space hN | N x <= r].
Proof.
move=> he r; have [B [hB ho]] := finite_basis_inner_product_witness he.
pose C := \sum_i N (e i).
have hC : 0 <= C by apply: sumr_ge0=> i _; exact: real_seminorm_nonnegative hN.1 _.
have hc := @inner_to_given_norm_continuous R V B hB N hN C hC
  (@finite_seminorm_inner_upper_bound R V B hB N hN.1 n e he ho).
have hK := @finite_norm_ball_compact R V B hB N hN n e he r.
have hset : [set x : real_norm_metric_space hN | N x <= r] =
    (fun x : inner_metric_space hB => (x : real_norm_metric_space hN)) @`
      [set x : inner_metric_space hB | N x <= r].
  apply/seteqP; split=> x hx; first by exists x.
  by have [y hy <-] := hx.
rewrite hset; apply: continuous_compact hK; exact: continuous_subspaceT hc.
Qed.
