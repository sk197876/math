(** Federer (1969), 2.10.20, p. 182: compact decreasing sets eventually lie
    in every open neighbourhood of their intersection. This supporting
    general-topology fact supplies both compact-sequence statements. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.

(** Source for [compact_decreasing_eventually_in_open]: supporting
    compactness step in both final assertions of
    2.10.20, p. 182. Closed decreasing subsets of
    one compact initial set suffice, including empty
    sets and an empty intersection. *)
Lemma compact_decreasing_eventually_in_open (X : topologicalType)
    (C : nat -> set X) (V : set X) :
  compact (C 0%N) -> (forall n, closed (C n)) ->
  (forall n m, (n<=m)%N -> C m `<=` C n) ->
  open V -> (\bigcap_n C n) `<=` V ->
  exists N, forall n, (N<=n)%N -> C n `<=` V.
Proof.
move=> hC0 hclosed hdec hV hKV.
pose U n := V `|` ~` C n.
have hU n : open (U n) := openU hV (closed_openC (hclosed n)).
have hcover : C 0%N `<=` \bigcup_(n in [set: nat]) U n.
  move=> x hx; case: (pselect (V x))=> hv.
  - exists 0%N=> //; by left.
  - have [n hn] : exists n, ~ C n x.
      apply: contrapT=> hnone; apply: hv; apply: hKV=> n _.
      apply: contrapT=> hn; apply: hnone; by exists n.
    exists n=> //; by right.
have [F hF hcov] := @compact_open_finite_cover X [the choiceType of (nat : Type)]
  setT U (C 0%N) hC0 (fun n _ => hU n) hcover.
pose N := \max_(i <- F) i.
have hN i (hi : i \in F) : (i<=N)%N.
  apply: leq_bigmax_seq; first exact hi; by [].
exists N=> n hn x hx.
have hx0 : C 0%N x := hdec 0%N n (leq0n n) x hx.
have [i hi hxi] := hcov x hx0.
case: hxi=> // hnot; exfalso; apply: hnot.
exact: hdec i n (leq_trans (hN i hi) hn) x hx.
Qed.
