(** Federer (1969), 4.1.2, p. 347: continuity in the base
    point of every fixed directional difference quotient. This
    proves the Borel domain needed for the reflexive input case. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP NormedCurveDerivativeUP
  NormMetricContinuity NormMetricScaleContinuity NormMetricSubtractContinuity
  TopologicalProductMaps TopologicalBorel PuncturedNormLimitLocusBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_directional_quotient_continuous]: the fixed-increment
    quotient used for D_j f in Federer 4.1.2, p. 347, is continuous
    as a function of the original source point. *)
Theorem norm_directional_quotient_continuous (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (f:X->Y) (v:X):
  continuous (f:real_norm_metric_space hNX->real_norm_metric_space hNY) ->
  forall t:R,continuous (fun x:real_norm_metric_space hNX=>
    (t^-1*:(f (x+t*:v)-f x):real_norm_metric_space hNY)).
Proof.
move=>hF t.
pose TX:=real_norm_metric_space hNX.
pose TY:=real_norm_metric_space hNY.
have hShift:continuous (fun x:TX=>(x+t*:v:TX)).
  have hId:continuous (fun x:TX=>x) by move=>x; exact:cvg_id.
  have hConst:continuous (fun _ : TX=>(t*:v:TX)) by move=>x; apply:cvg_cst; exact:nbhs_filter.
  have hPair:=topological_pair_continuous hId hConst.
  move=>x; exact:(continuous_comp (hPair x) (@real_norm_metric_add_continuous R X NX hNX (x,t*:v))).
have hFT:continuous (fun x:TX=>(f (x+t*:v):TY)).
  move=>x; exact:(continuous_comp (hShift x) (hF (x+t*:v))).
have hPair:=topological_pair_continuous hFT hF.
have hDiff:continuous (fun x:TX=>(f (x+t*:v)-f x:TY)).
  move=>x; exact:(continuous_comp (hPair x)
    (@real_norm_metric_subtract_continuous R Y NY hNY (f (x+t*:v),f x))).
move=>x; exact:(continuous_comp (hDiff x)
  (@real_norm_metric_scale_continuous R Y NY hNY t^-1 (f (x+t*:v)-f x))).
Qed.

(** Source for [norm_directional_derivative_domain_borel]: the domain
    of the full two-sided norm derivative D_v f is Borel for continuous
    f with Banach target, supporting the locally Lipschitz/reflexive
    commutation of Federer 4.1.2, p. 347. *)
Theorem norm_directional_derivative_domain_borel (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY)) (f:X->Y) (v:X):
  continuous (f:real_norm_metric_space hNX->real_norm_metric_space hNY) ->
  @borel_set (real_norm_metric_space hNX)
    [set x|exists w:Y,punctured_norm_limit NY (fun t=>t^-1*:(f (x+t*:v)-f x)) w].
Proof.
move=>hF; exact:(@punctured_norm_limit_locus_borel R
  [the topologicalType of real_norm_metric_space hNX] Y NY hNY hY
  (fun x t=>t^-1*:(f (x+t*:v)-f x))
  (@norm_directional_quotient_continuous R X Y NX NY hNX hNY f v hF)).
Qed.
