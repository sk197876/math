(** Federer (1969), 3.4.8(11), p. 333:
    the boundary of a component of an
    open normed-space set lies outside that set.
    Existing convex-ball connectedness supplies the
    local connected neighbourhoods used here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormBoundedLinearTopology NormLinearDomainLaws NormConvexConnected.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_open_component_boundary_outside]:
    the component boundary used for the
    zero-boundary assertion of Psi in
    3.4.8(11), p. 333. This supporting
    result applies in every normed source. *)
Theorem norm_open_component_boundary_outside (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set X) a x:
  @open (real_norm_metric_space hNX) A ->
  @closure (real_norm_metric_space hNX)
    (@connected_component (real_norm_metric_space hNX) A a) x ->
  ~@interior (real_norm_metric_space hNX)
    (@connected_component (real_norm_metric_space hNX) A a) x ->~A x.
Proof.
move=>hOpen hClosure hNotInterior hAx.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose C:=@connected_component T A a.
have hNbhs:(nbhs (x:T)) A by move:hOpen;rewrite openE;exact.
have [r [hr hBall]]:=(@norm_domain_interior_neighbourhood R X NX hNX A x).2 hNbhs.
pose U:set X:=[set y|NX (y-x)<r].
have hUx:U x.
  change (NX (x-x)<r);by rewrite subrr (real_seminorm_zero hNX.1).
have hUA:U `<=` A.
  move=>y hy;have h:=hBall (y-x) hy;by rewrite addrC subrK in h.
have hUOpen:@open T U.
  rewrite openE=>y hy.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX U y).1
    (@norm_open_ball_domain_interior R X NX hNX x r y hy).
have hUNbhs:(nbhs (x:T)) U by move:hUOpen;rewrite openE;exact.
have [b [hCb hUb]]:=hClosure U hUNbhs.
have hConnectedU:@connected T U:=@norm_inner_convex_connected R X NX hNX U
  (@norm_open_ball_convex R X NX hNX x r).
have hUC:U `<=` C.
  have hSame:=@same_connected_component T A a b hCb.
  rewrite /C hSame;exact:(@connected_component_max T A U b hUb hUA hConnectedU).
apply:hNotInterior.
apply:(filterS hUC);exact:hUNbhs.
Qed.
