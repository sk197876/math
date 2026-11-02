(** Federer (1969), proof of 2.4.6, p. 84: passing a bound through the
    limits of finitely many increasing nonnegative summands. We pass each
    summand through the bound and synchronize the finitely many sequence
    indices by their maximum. This avoids any external integration or
    convergence theorem. Source context: ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit ExtendedRealLimitBounds
  ExtendedLowerLimitUP ExtendedLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_nonnegative_limit_add_bound]: supporting
    passage of a fixed nonnegative addend through a limiting
    upper bound in Federer 2.4.6, p. 84. *)
Lemma extended_nonnegative_limit_add_bound (R : realType)
    (u : nat -> \bar R) a b c :
  (forall n, 0 <= u n) -> extended_order_limit u a ->
  0 <= b -> (forall n, u n + b <= c) -> a + b <= c.
Proof.
move=> hp hl; case: b=> [r| |] hb hc; last by [].
- rewrite -leeBrDr //; apply: (@extended_order_limit_upper_bound R u a (c-r%:E) hl)=> n.
  rewrite leeBrDr //; exact: hc.
- have hn : u 0%N != -oo by rewrite gt_eqF //; exact: lt_le_trans (ltNyr 0%R) (hp 0%N).
  have h := hc 0%N; rewrite addey // in h.
  exact: le_trans (leey _) h.
Qed.

(** Source for [nonnegative_increasing_finite_sum_bound]: the
    finite-family limiting inequality in Federer 2.4.6, p. 84;
    the sequence list may be empty and limits may be infinite. *)
Lemma nonnegative_increasing_finite_sum_bound (R : realType) (I : eqType)
    (s0 : seq I) (v : I -> nat -> \bar R) (a : I -> \bar R) c :
  (forall i, i \in s0 -> forall n, 0 <= v i n) ->
  (forall i, i \in s0 -> extended_increases_to (v i) (a i)) ->
  (forall n, (\sum_(i <- s0) v i n) <= c) -> (\sum_(i <- s0) a i) <= c.
Proof.
have aux : forall s : seq I,
    (forall i, i \in s -> forall n, 0 <= v i n) ->
    (forall i, i \in s -> extended_increases_to (v i) (a i)) ->
    forall b c, 0 <= b ->
    (forall n, (\sum_(i <- s) v i n) + b <= c) -> (\sum_(i <- s) a i) + b <= c.
  elim=> [|i s ih] hp hl b d hb hd; first by move: (hd 0%N); rewrite !big_nil.
  have hpi := hp i (mem_head i s).
  have hli := hl i (mem_head i s).
  have hps j : j \in s -> forall n, 0 <= v j n.
    move=> hj; apply: hp; by rewrite in_cons hj orbT.
  have hls j : j \in s -> extended_increases_to (v j) (a j).
    move=> hj; apply: hl; by rewrite in_cons hj orbT.
  have hsa : 0 <= \sum_(j <- s) a j.
    rewrite big_seq; apply: sume_ge0=> j hj.
    exact (@extended_order_limit_lower_bound R (v j) (a j) 0 (hls j hj).2 (hps j hj)).
  rewrite big_cons -addeA.
  apply: (@extended_nonnegative_limit_add_bound R (v i) (a i) ((\sum_(j <- s) a j)+b) d
    hpi hli.2 (adde_ge0 hsa hb))=> k.
  rewrite addeCA.
  apply: (ih hps hls (v i k+b) d (adde_ge0 (hpi k) hb))=> n.
  pose m := maxn k n.
  have hsum : (\sum_(j <- s) v j n) <= \sum_(j <- s) v j m.
    rewrite !big_seq; apply: lee_sum=> j hj; exact: (hls j hj).1 n m (leq_maxr k n).
  have hi : v i k <= v i m := hli.1 k m (leq_maxl k n).
  apply: le_trans (leeD hsum (leeD hi (lexx b))) _.
  rewrite addeCA addeA; have hh := hd m; by rewrite big_cons in hh.
move=> hp hl hc.
have h := aux s0 hp hl 0 c (lexx 0).
rewrite adde0 in h; apply: h=> n; by rewrite adde0.
Qed.

(** Source for [nonnegative_increasing_finite_lower_limit]: the
    finite-family lower-limit comparison used in Federer 2.4.6, p. 84 *)
Lemma nonnegative_increasing_finite_lower_limit (R : realType) (I : eqType)
    (s : seq I) (v : I -> nat -> \bar R) (a : I -> \bar R) (u : nat -> \bar R) :
  (forall i, i \in s -> forall n, 0 <= v i n) ->
  (forall i, i \in s -> extended_increases_to (v i) (a i)) ->
  (forall n, (\sum_(i <- s) v i n) <= u n) ->
  (\sum_(i <- s) a i) <= extended_lower_limit u.
Proof.
move=> hp hl hu; apply: (@nonnegative_increasing_finite_sum_bound R I s v a _ hp hl)=> n.
apply: (extended_lower_limit_eventual_bound (extended_lower_limit_laws u)).
exists n=> m hnm; apply: le_trans _ (hu m).
rewrite !big_seq; apply: lee_sum=> i hi; exact: (hl i hi).1 n m hnm.
Qed.
