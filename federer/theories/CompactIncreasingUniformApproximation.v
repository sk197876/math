(** Federer (1969), 2.5.13, pp. 106–107: the decreasing compact sets where
    g-h_n exceeds a fixed positive error eventually become empty. We use its
    equivalent finite-open-subcover form, including empty compact sets. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals constructive_ereal topology.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import RealMetricBackground ExtendedRealOrderLimit MonotoneDaniellIntegralUP CompactFiniteCover CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_increasing_uniform_approximation]: the eventual
    uniform error bound on the compact support in Federer 2.5.13, p. 107
    This supporting lemma allows any compact K and does not require
    nonnegative functions; positivity is used later to extend the support
    estimate to the whole space. *)
Lemma compact_increasing_uniform_approximation (R : realType) (X : topologicalType)
    (K : set X) (f : nat -> X -> R) (g : X -> R) (e : R) :
  compact K -> (forall n, continuous (f n : X -> real_line_metric R)) ->
  continuous (g : X -> real_line_metric R) -> real_functions_increase_to f g ->
  0 < e -> exists N, forall n, (N <= n)%N -> forall x, K x -> g x-f n x < e.
Proof.
move=> hK hf hg hi he.
pose U n := [set x | g x-f n x < e].
have ho n : open (U n).
  have hd : continuous (fun x : X => (g x-f n x : real_line_metric R)).
    move=> x; exact: (@continuousB R R^o X g (f n) x (hg x) (hf n x)).
  exact ((@continuousP X (real_line_metric R) (fun x => g x-f n x)).1 hd
    [set r | r < e] (@order_strict_lower_ray_open _ [the orderTopologicalType _ of R^o] e)).
have hcov : K `<=` \bigcup_(n in (@setT nat)) U n.
  move=> x hx.
  have hlow : ((g x-e)%:E < (g x)%:E)%E by rewrite lte_fin ltrBlDr ltrDl.
  have [N hN] := (hi x).2.1 _ hlow.
  have hh : g x-e < f N x := hN N (leqnn N).
  exists N=> //; change (g x-f N x < e).
  by rewrite ltrBlDr addrC -ltrBlDr.
have [F hF hcover] := @compact_open_finite_cover X [the choiceType of (nat : Type)]
  setT U K hK (fun n _ => ho n) hcov.
pose N := \max_(i <- F) i.
have hN i : i \in F -> (i <= N)%N.
  move=> h; apply: leq_bigmax_seq; first exact h; by [].
exists N=> n hn x hx.
have [i hiF hix] := hcover x hx.
have hle : f i x <= f n x := (hi x).1 i n (leq_trans (hN i hiF) hn).
apply: le_lt_trans _ hix.
by rewrite lerD2l lerN2.
Qed.
