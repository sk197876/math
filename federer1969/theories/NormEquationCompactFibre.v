(** Federer (1969), 3.4.8(10), p. 332:
    the original equations over a compact
    prefix set form a compact fibre.
    This supporting connection applies the existing
    common-zero closedness and finite-dimensional compact-ball
    theorems after the separate coordinate bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground LinearBasis NormDifferentialUP
  NormBoundedLinearTopology NormClassOneUP NormCommonZeroClosed FiniteNormMetricCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_equation_compact_fibre]:
    closedness and the separately proved uniform
    coordinate bound give compactness of
    Z intersect p_m inverse(C),
    3.4.8(10), p. 332. The equations
    need continuity only on their original
    cylinder; no global analytic extension is used. *)
Theorem norm_equation_compact_fibre (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    d (e:'I_d->X) (he:is_basis e) (P:Hom X Y) (U C:set Y)
    (index:Type) (f:index->X->R) (delta:Y->R) (Z:set X):
  norm_bounded_linear NX NY P ->
  compact [set y:real_norm_metric_space hNY|C y] ->C `<=` U ->
  (forall y,C y ->delta y<>0) ->
  (forall j,norm_class_zero NX (fun t:R^o=>`|t|) (fun x=>U (P x)) (f j)) ->
  (forall x,Z x <->U (P x) /\(forall j,f j x=0) /\delta (P x)<>0) ->
  (exists M:R,forall x,Z x ->C (P x) ->NX x<=M) ->
  compact [set x:real_norm_metric_space hNX|Z x /\C (P x)].
Proof.
move=>hP hCompact hCU hDelta hF hZ [M hBound].
pose Q:set X:=fun x=>C (P x).
have hClosedC:@closed (real_norm_metric_space hNY) C:=
  compact_closed (@metric_hausdorff R (real_norm_metric_space hNY)) hCompact.
have hContinuous:=@norm_bounded_linear_continuous R X Y NX NY hNX hNY P hP.
have hClosedQ:@closed (real_norm_metric_space hNX) Q.
  apply:preimage_closed hClosedC=>x _;exact:hContinuous x.
have hQA:Q `<=` (fun x=>U (P x)) by move=>x hx;exact:hCU (P x) hx.
have hSet:[set x:X|Z x /\C (P x)] = Q `&` [set x|forall j,f j x=0].
  apply/seteqP;split.
  - move=>x [hz hc];split;first exact:hc.
    exact:((hZ x).1 hz).2.1.
  - move=>x [hc hZero];split;last exact:hc.
    apply:(hZ x).2;split;first exact:hCU (P x) hc.
    split;first exact:hZero.
    exact:hDelta (P x) hc.
have hClosed:@closed (real_norm_metric_space hNX) [set x:X|Z x /\C (P x)].
  rewrite hSet.
  exact:(@norm_common_zero_on_closed_subset R X R^o NX (fun t:R^o=>`|t|) hNX
    (@scalar_absolute_value_norm R) (fun x=>U (P x)) Q index f hF hQA hClosedQ).
have hBall:=@finite_norm_metric_ball_compact R X NX hNX d e he M.
apply:(subclosed_compact hClosed hBall)=>x [hz hc];exact:hBound x hz hc.
Qed.
