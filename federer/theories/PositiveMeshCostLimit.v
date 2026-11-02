(** Federer (1969), 2.10.45, printed p. 203: pass the product covering
    estimate to the exact diameter cost. The printed mesh equals diam(T)>0.
    To include diameter-zero generators in arbitrary metric factors, use
    positive meshes slightly above their actual diameters and polynomial
    cost continuity. No containing positive-diameter set in that factor is
    assumed. This keeps isolated points and degree zero. Source context:
    SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology lra.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBounds HausdorffDiameterCost HausdorffGaugeContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_mesh_cost_limit]: supporting
    extension of the diameter-mesh estimate in
    2.10.45, p. 203, to zero diameters.
    A finite positive coefficient is unchanged
    when positive meshes decrease to any nonnegative d.
    The quantity being bounded may initially be infinite. *)
Theorem positive_mesh_cost_limit (R : realType) k (d t K : R) (x : \bar R) :
  (0<K)%R -> (0<=d)%R -> (d<t)%R ->
  (forall h : R, (0<h)%R -> (d<=h)%R -> (h<t)%R ->
    x<=(K*(hausdorff_normalisation R k*h^+k))%R%:E) ->
    x<=(K*(hausdorff_normalisation R k*d^+k))%R%:E.
Proof.
move=> hK hd hdt hbound; rewrite leNgt; apply/negP=> hbad.
have [q [hbq hqx]] := @extended_rationals_order_dense R
  (K*(hausdorff_normalisation R k*d^+k))%R%:E x hbad.
have hb0 : (K*(hausdorff_normalisation R k*d^+k)<ratr q)%R by move: hbq; rewrite lte_fin.
have hb : (hausdorff_normalisation R k*d^+k<ratr q/K)%R.
  by rewrite ltr_pdivlMr // mulrC.
have [e [he [hcap hcost]]] := @hausdorff_real_gauge_small_enlargement R k d t (ratr q/K)%R hdt hb.
have hp : (0<d+e+e)%R by lra.
have hdmesh : (d<=d+e+e)%R by lra.
have hh := hbound (d+e+e)%R hp hdmesh hcap.
have hcostR : (K*(hausdorff_normalisation R k*(d+e+e)^+k)<ratr q)%R.
  move: hcost; by rewrite ltr_pdivlMr // mulrC.
have hlt : x<(ratr q : R)%:E.
  apply: le_lt_trans hh _; by rewrite lte_fin.
by have hf := lt_trans hqx hlt; rewrite ltxx in hf.
Qed.
