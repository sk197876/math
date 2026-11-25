(** Finite missing-cap iteration in Federer (1969), 2.10.31, p. 196. This is
    the printed induction on the finitely many cap centres. The existential
    intermediate compact sets remain inside the given class; no recursion
    operator or unproved choices are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric CompactSetDistanceProfile
  CompactHausdorffMetric MetricClosedBalls SteinerStableFamilyUP SteinerMissingCap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_finite_missing_caps]: direct
    finite iteration T_0,...,T_k in 2.10.31,
    p. 196. The initial cap is retained even
    if the list of further centres is empty;
    repeated centres are harmless. *)
Theorem steiner_finite_missing_caps (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (C : set (compact_hausdorff_space (inner_metric_space hB)))
    (S : compact_hausdorff_space (inner_metric_space hB))
    (a : inner_metric_space hB) (r e : R) (s : seq (inner_metric_space hB)) :
  is_steiner_stable_family hB C -> C S -> 0<=r ->
  (forall x, val S x -> inner_norm hB x<=r) ->
  inner_norm hB a=r -> (forall y, y \in s -> inner_norm hB y=r) ->
  (forall x, inner_norm hB x=r -> metric_closed_ball a e x -> ~val S x) ->
  exists T : compact_hausdorff_space (inner_metric_space hB),
    C T /\ (forall x, val T x -> inner_norm hB x<=r) /\
    (forall x, inner_norm hB x=r -> metric_closed_ball a e x -> ~val T x) /\
    (forall y, y \in s -> forall x, inner_norm hB x=r -> metric_closed_ball y e x -> ~val T x).
Proof.
move=> hC hS hr hb ha.
elim: s=> [|y s IH] hs hmiss.
- exists S; split=> //; split=> //; split=> // y; by rewrite in_nil.
- have hs0 z : z \in s -> inner_norm hB z=r.
    by move=> hz; apply: hs; rewrite in_cons hz orbT.
  have [T [hT [hTb [hTa hTs]]]] := IH hs0 hmiss.
  have hy : inner_norm hB y=r by apply: hs; rewrite in_cons eqxx.
  have [U [hU [hUb [hretain hUy]]]] :=
    steiner_move_missing_cap hC hT hr hTb ha hy hTa.
  exists U; split=> //; split=> //; split.
  + move=> x hx hax; exact: hretain x hx (hTa x hx hax).
  + move=> z; rewrite in_cons=> /orP[/eqP ->|hz] x hx hzx.
    * exact: hUy x hx hzx.
    * exact: hretain x hx (hTs z hz x hx hzx).
Qed.
