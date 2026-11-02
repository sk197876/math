(** Federer (1969), 2.3.2(2), p. 73: private countable dense refinement.
    Pick one point of the dense subset in each nonempty interval with
    endpoints in the original countable order-dense family. A supplied
    member handles empty intervals. Source context:
    DenseOrderRefinementUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets topology.
From Federer Require Import CountableOrderIntervals DenseOrderRefinementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope order_scope.
Local Open Scope classical_set_scope.

(** Source for [dense_order_refinement_exists]: supporting choice argument
    for the arbitrary dense-subset criterion in Federer 2.3.2(2), p. 73
    Topological density and the original order-dense family ensure every
    required open interval has an admissible point. *)
Theorem dense_order_refinement_exists disp (Y : orderTopologicalType disp)
    (J : Type) (d : J -> Y) (D : set Y) (y0 : Y) :
  is_order_dense_family d -> dense D -> D y0 ->
  exists e : J * J -> Y, is_dense_order_refinement D e.
Proof.
move=> hd hD hy0.
have hbetween a b : a < b -> exists y, D y /\ a < y /\ y < b.
  move=> hab; have [j [haj hjb]] := hd a b hab.
  have hn : (`]a,b[%classic : set Y) !=set0.
    exists (d j); by rewrite /= interval.in_itv /= haj hjb.
  have [y [hy hDy]] := hD _ hn (itv_open a b).
  move: hy; rewrite /= interval.in_itv /= => /andP[hay hyb].
  by exists y.
have hp p : exists y, D y /\ (d p.1 < d p.2 -> d p.1 < y /\ y < d p.2).
  case: (pselect (d p.1 < d p.2))=> [hab|hn].
  - have [y [hy [ha hb]]] := hbetween _ _ hab; by exists y; split=> // _; split.
  - exists y0; split=> // h; exfalso; exact: hn h.
pose e p := projT1 (cid (hp p)).
have he p : D (e p) /\ (d p.1 < d p.2 -> d p.1 < e p /\ e p < d p.2).
  exact: projT2 (cid (hp p)).
exists e; constructor; first by move=> p; exact: (he p).1.
move=> a b hab.
have [i [hai hib]] := hd a b hab.
have [j [hij hjb]] := hd (d i) b hib.
exists (i,j); have [hil hlj] := (he (i,j)).2 hij.
split; [exact: lt_trans hai hil|exact: lt_trans hlj hjb].
Qed.
