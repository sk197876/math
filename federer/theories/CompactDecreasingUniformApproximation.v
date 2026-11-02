(** Federer (1969), 2.5.14, p. 108: the argument of 2.5.13, pp. 106–107,
    applies to decreasing continuous vector norms. This is the order-dual
    form of the already proved scalar compact-cover estimate. Other source
    conventions: OrderBoundedVectorFunctionalUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import RealMetricBackground CompactIncreasingUniformApproximation
  MonotoneDaniellIntegralUP ExtendedRealOrderLimit ExtendedRealDecreasingLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_decreasing_uniform_approximation]:
    eventual uniform smallness on a compact set, supporting
    the removal of the sequence-continuity condition in Federer
    2.5.14, p. 108, by the proof of 2.5.13, p. 107. *)
Lemma compact_decreasing_uniform_approximation (R : realType) (X : topologicalType)
    (K : set X) (g : nat -> X -> R) (e : R) :
  compact K -> (forall n, continuous (g n : X -> real_line_metric R)) ->
  (forall x, extended_decreases_to (fun n=>(g n x)%:E) (0 : R)%:E) ->
  0<e -> exists M, forall n, (M<=n)%N -> forall x, K x -> g n x<e.
Proof.
move=> hK hg hdec he.
pose f := fun n x=> -g n x.
have hf n : continuous (f n : X -> real_line_metric R).
  move=> x; exact: (@continuousN R R^o X (g n) x (hg n x)).
have hi : real_functions_increase_to f (fun _=>0).
  move=> x; split.
  - move=> n m hnm; rewrite lee_fin lerN2; exact: (hdec x).1 n m hnm.
  - have hn := extended_order_limit_negate (hdec x).2.
    by rewrite -EFinN oppr0 in hn.
have [M hM] := @compact_increasing_uniform_approximation R X K f (fun _=>0) e
  hK hf (@cst_continuous X (real_line_metric R) 0) hi he.
exists M=> n hn x hx; have hh := hM n hn x hx; by rewrite /f sub0r opprK in hh.
Qed.
