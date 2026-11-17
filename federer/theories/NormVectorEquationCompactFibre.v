(** Federer (1969), 3.4.12, p. 339, extending compact
    polynomial fibres in 3.4.8(10), p. 332. The existing common-zero
    closedness theorem allows any normed target. Connect it directly
    to finite-dimensional compact balls; complex equations need no
    scalar-valued replacement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis NormDifferentialUP
  NormBoundedLinearTopology NormClassOneUP NormCommonZeroClosed FiniteNormMetricCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_vector_equation_compact_fibre]:
    continuous equations cut a closed set over a compact
    prefix set. A separately established norm bound makes that
    set compact, supporting 3.4.12, p. 339. The equations need
    continuity only on the original cylinder. *)
Theorem norm_vector_equation_compact_fibre (R:realType) (X Y T:lmodType R)
    (NX:X->R) (NY:Y->R) (NT:T->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNT:is_real_norm NT)
    d (e:'I_d->X) (he:is_basis e) (P:Hom X Y) (U C:set Y)
    (index:Type) (f:index->X->T) (Z:set X):
  norm_bounded_linear NX NY P ->
  compact [set y:real_norm_metric_space hNY|C y] ->C `<=` U ->
  (forall j,norm_class_zero NX NT (fun x=>U (P x)) (f j)) ->
  (forall x,C (P x) ->(Z x <->forall j,f j x=0)) ->
  (exists M:R,forall x,Z x ->C (P x) ->NX x<=M) ->
  compact [set x:real_norm_metric_space hNX|Z x /\C (P x)].
Proof.
move=>hP hCompact hCU hF hZ [M hBound].
pose Q:set X:=fun x=>C (P x).
have hClosedC:@closed (real_norm_metric_space hNY) C:=
  compact_closed (@metric_hausdorff R (real_norm_metric_space hNY)) hCompact.
have hContinuous:=@norm_bounded_linear_continuous R X Y NX NY hNX hNY P hP.
have hClosedQ:@closed (real_norm_metric_space hNX) Q.
  apply:preimage_closed hClosedC=>x _;exact:hContinuous x.
have hQA:Q `<=` (fun x=>U (P x)) by move=>x hx;exact:hCU (P x) hx.
have hSet:[set x:X|Z x /\C (P x)]=Q `&` [set x|forall j,f j x=0].
  apply/seteqP;split.
  - move=>x [hz hc];split;first exact:hc;exact:(hZ x hc).1 hz.
  - move=>x [hc hZero];split;last exact:hc;exact:(hZ x hc).2 hZero.
have hClosed:@closed (real_norm_metric_space hNX) [set x:X|Z x /\C (P x)].
  rewrite hSet.
  exact:(@norm_common_zero_on_closed_subset R X T NX NT hNX hNT
    (fun x=>U (P x)) Q index f hF hQA hClosedQ).
have hBall:=@finite_norm_metric_ball_compact R X NX hNX d e he M.
apply:(subclosed_compact hClosed hBall)=>x [hz hc];exact:hBound x hz hc.
Qed.
