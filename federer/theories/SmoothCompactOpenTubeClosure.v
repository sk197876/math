(** Federer (1969), 4.1.14, p. 370: choose the source neighbourhood Z
    so that its closure is a compact subset of the original open U.
    This supporting form of 4.1.2, p. 348, keeps every sufficiently
    small open tube about the same compact K inside one compact set.
    Empty compact sets and zero-dimensional sources remain allowed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  LinearBasis NormBoundedLinearTopology SmoothCompactSet
  SmoothCompactInteriorThickening MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_compact_open_tube_closure]: the compact-closure
    neighbourhood required in the smoothing paragraph of Federer
    4.1.14, p. 370. The radius is chosen once, before any smoothing
    scale; no point of K is selected. *)
Theorem smooth_compact_open_tube_closure (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b)
    (U:set X) (hU:forall x,U x ->norm_domain_interior NX U x)
    (K:smooth_compact_set hNX U):
  exists r0:R,0<r0 /\ forall r:R,0<r ->r<=r0 ->
    @compact (real_norm_metric_space hNX)
      (@closure (real_norm_metric_space hNX)
        (@metric_open_thickening R (real_norm_metric_space hNX)
          (smooth_compact_carrier K) r)) /\
    @closure (real_norm_metric_space hNX)
      (@metric_open_thickening R (real_norm_metric_space hNX)
        (smooth_compact_carrier K) r) `<=` U.
Proof.
have[r0 [hr0 [C [hKC hTube]]]]:=
  @smooth_compact_interior_thickening R X NX hNX n b hb U hU K.
exists r0;split;first exact:hr0.
move=>r hr hrr0.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose Z:=@metric_open_thickening R (real_norm_metric_space hNX)
  (smooth_compact_carrier K) r.
have hZC:Z `<=` smooth_compact_carrier C.
  move=>x [a ha hax].
  have hNear:NX (x-a)<=r0.
    change (is_true (NX (a-x)<r)) in hax.
    rewrite (real_seminorm_subtract hNX.1).
    exact:(le_trans (ltW hax) hrr0).
  exact:(hTube x a ha hNear).
have hClosedC:@closed T (smooth_compact_carrier C):=
  compact_closed (@metric_hausdorff R (real_norm_metric_space hNX))
    (smooth_compact_is_compact C).
have hClosureC:@closure T Z `<=` smooth_compact_carrier C.
  have h:=@closureS T Z (smooth_compact_carrier C) hZC.
  by rewrite -((@closure_id T (smooth_compact_carrier C)).1 hClosedC) in h.
split.
- have hEqual:@closure T Z = smooth_compact_carrier C `&` @closure T Z.
    apply/seteqP;split.
    + move=>x hx;split;[exact:hClosureC x hx|exact:hx].
    + by move=>x [_ hx].
  rewrite hEqual.
  exact:compact_closedI (smooth_compact_is_compact C) (@closed_closure T Z).
- move=>x hx;exact:(smooth_compact_in_domain C x (hClosureC x hx)).
Qed.
