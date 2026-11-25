(** Federer (1969), 4.1.14, p. 371: a cutoff of the
    original locally Lipschitz map has a locally Lipschitz ambient
    zero extension. The closed cutoff support lies inside the
    original open domain. The neighbourhood argument is the same
    localization used in 3.1.13, p. 225. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology SmoothZeroExtension LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_zero_extended_locally_lipschitz]: the local
    smoothing on an original open domain in Federer 4.1.14,
    p. 371. No regularity of the arbitrary outside representative
    is assumed, and no target-domain value is selected. *)
Theorem norm_zero_extended_locally_lipschitz (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U C:set X) (f:X->Y):
  (forall x,U x->norm_domain_interior NX U x) ->
  @closed (real_norm_metric_space hNX) C ->C `<=` U ->
  (forall x,U x->~C x->f x=0) ->
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) U f ->
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) setT (norm_zero_extended_function U f).
Proof.
move=>hU hC hCU hOff hLocal a _.
case:(pselect (U a))=>[ha|ha].
- have[V [hV [L [hL hBound]]]]:=hLocal a ha.
  have hUa:nbhs (a:real_norm_metric_space hNX) U:=
    (@norm_domain_interior_neighbourhood R X NX hNX U a).1 (hU a ha).
  exists (U `&` V);split;first exact:filterI hUa hV.
  exists L;split;first exact:hL.
  split;first exact:hBound.1.
  move=>x y [_ [hUx hVx]] [_ [hUy hVy]].
  rewrite !norm_zero_extended_function_on //.
  exact:hBound.2 x y (conj hUx hVx) (conj hUy hVy).
- have hNotC:~C a by move=>hCa;exact:ha (hCU a hCa).
  have hOpen:@open (real_norm_metric_space hNX) (~`C):=closed_openC hC.
  have hNeighbourhood:nbhs (a:real_norm_metric_space hNX) (~`C):=
    open_nbhs_nbhs (conj hOpen hNotC).
  have hZero:forall x,~C x->norm_zero_extended_function U f x=0.
    move=>x hx;case:(pselect (U x))=>[hUx|hUx].
    + rewrite norm_zero_extended_function_on //;exact:hOff x hUx hx.
    + exact:(@norm_zero_extended_function_off X Y U f x hUx).
  exists (~`C);split;first exact:hNeighbourhood.
  exists 1;split;first exact:ltr01.
  split;first exact:ler01.
  move=>x y [_ hx] [_ hy].
  rewrite (hZero x hx) (hZero y hy).
  change (is_true (NY (0-0)<=1*NX (x-y))).
  rewrite subrr (real_seminorm_zero hNY.1) mul1r.
  exact:real_seminorm_nonnegative hNX.1 _.
Qed.
