(** Federer (1969), 4.1.1, pp. 344–345: derivatives vanish
    off the original compact support. This supports the printed
    distribution estimate using nu^i_K for that same K, rather
    than an auxiliary larger compact set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialLocal
  NormHigherDifferentialSupport SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothFunctionDerivativesUP SmoothDerivativeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SmoothSupportDerivatives.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x -> norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation evZ := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation support := (@smooth_function_support R X Y NX hNX U E ev).

(** Source for [smooth_derivative_outside_compact_support]: every
    derivative vanishes outside K when spt phi is contained in K,
    supporting the fixed-support estimates of Federer 4.1.1,
    p. 345. The claim includes derivative order zero. *)
Theorem smooth_derivative_outside_compact_support
    (K:smooth_compact_set hNX U) f :
  support f `<=` smooth_compact_carrier K ->
  forall k x,~smooth_compact_carrier K x -> @D k x f=0.
Proof.
move=>hK k x hx.
case:(pselect (U x))=>[hUx|hUx]; last exact:(smooth_derivative_outside hD k f hUx).
have hClosed:=compact_closed (@metric_hausdorff R (real_norm_metric_space hNX))
  (smooth_compact_is_compact K).
have hOpen:=closed_openC hClosed.
have hInterior y (hy:~smooth_compact_carrier K y):
    norm_domain_interior NX (fun z=>~smooth_compact_carrier K z) y.
  apply:(norm_domain_interior_neighbourhood hNX _ y).2.
  by move:hOpen; rewrite openE; apply.
have hZero:=@norm_higher_differential_locally_zero R X Y NX NY hNX hNY
  Z evZ ZN hZ (fun y=>~smooth_compact_carrier K y) (ev f) k x
  hInterior ((smooth_function_compact_support_iff hE K f).1 hK) hx.
have hRestr:=@norm_higher_differential_open_restriction R X Y NX NY hNX hNY
  Z evZ ZN hZ k (fun _=>True) U (ev f) (fun y hy=>Logic.I) hU x hUx 0.
exact:(norm_higher_differential_unique hNX hNY hZ
  (@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD k f x hUx)
  (hRestr.1 hZero)).
Qed.

(** Source for [smooth_supported_seminorm_bound]: on D_K the
    seminorm nu^i_K dominates nu^i_L for every other compact L,
    supporting the exact local continuity criterion in Federer
    4.1.1, p. 345. No compact enlargement is added to that criterion. *)
Theorem smooth_supported_seminorm_bound (K L:smooth_compact_set hNX U)
    i (p q:E->R) :
  @is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i p ->
  @is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D L i q ->
  forall f,support f `<=` smooth_compact_carrier K -> q f<=p f.
Proof.
move=>hp hq f hf.
apply:(@smooth_derivative_seminorm_least R X Y NX NY hNX hNY U E D L i q hq f
  (p f) (smooth_derivative_seminorm_nonnegative hp f))=>j hj x hx.
case:(pselect (smooth_compact_carrier K x))=>[hKx|hKx].
- exact:(smooth_derivative_seminorm_bound hp f hj hKx).
- rewrite (smooth_derivative_outside_compact_support hf j hKx)
    (real_seminorm_zero (continuous_multilinear_norm_is_norm hNY (hZ j)).1).
  exact:smooth_derivative_seminorm_nonnegative hp f.
Qed.
End SmoothSupportDerivatives.
