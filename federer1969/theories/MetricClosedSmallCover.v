(** Federer (1969), 3.1.9, p. 218: decomposition
    of each closed growth-center set into countably many closed
    pieces of small diameter. Empty center sets are allowed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import SeparableClosedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [separable_closed_small_cover_allow_empty]:
    the closed sets C_(j,k) in Federer 3.1.9, p. 218.
    This supporting form of 2.2.8 permits an empty parent;
    it asserts existence and does not expose an implementation
    of a chosen covering. *)
Theorem separable_closed_small_cover_allow_empty (R : realType) (X : metricType R)
    (D C : set X) (e : R) :
  countable D -> dense D -> closed C -> 0<e ->
  exists F : nat->set X,
    (forall k, closed (F k) /\ F k `<=` C /\
      forall x y, F k x -> F k y -> mdist x y<=e) /\
    C=\bigcup_k F k.
Proof.
move=> hc hd hC he.
case: (pselect (C!=set0))=> [hne|hempty].
- have [F [hF hcover]] := separable_closed_small_cover hc hd hC hne he.
  exists F; split=> // k; have [hclosed [_ [hsub hdiam]]] := hF k.
  by split=> //; split.
- have hzero : C=set0.
    apply/seteqP; split; last by [].
    move=> x hx; exfalso; apply: hempty; by exists x.
  exists (fun _=>set0); split.
  + move=> k; split; first exact: closed0.
    by split=> // x.
  + rewrite hzero; apply/seteqP; split; first by [].
    by move=> x [k _ hx].
Qed.
