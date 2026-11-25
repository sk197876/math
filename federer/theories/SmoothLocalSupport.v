(** Federer (1969), 4.1.1, p. 344: locality of higher
    differentials off a function's support. This connects the
    original closure definition to compact support bounds for
    continuous linear functionals. *)
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

Section LocalSupport.
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
Local Notation T := (real_norm_metric_space hNX).

(** Source for [smooth_derivative_outside_support]: every
    derivative is zero off spt phi in U, supporting the compact
    support assertion for E' in Federer 4.1.1, p. 344. *)
Theorem smooth_derivative_outside_support f x :
  U x -> ~support f x -> forall k,@D k x f=0.
Proof.
move=>hx hs k.
pose O:set X:=[set y|~closure [set z:T|ev f z<>0] y].
have hOpen:@open T O:=closed_openC (@closed_closure T _).
have hInterior y (hy:O y):norm_domain_interior NX O y.
  apply:(norm_domain_interior_neighbourhood hNX O y).2.
  by move:hOpen; rewrite openE; apply.
have hZero y:O y -> ev f y=0.
  move=>hy; case:(pselect (ev f y=0))=>// hn.
  exact:False_ind _ (hy (@subset_closure T _ y hn)).
have hOx:O x by move=>hc; apply:hs; split.
have hz:=@norm_higher_differential_locally_zero R X Y NX NY hNX hNY
  Z evZ ZN hZ O (ev f) k x hInterior hZero hOx.
have hRestr:=@norm_higher_differential_open_restriction R X Y NX NY hNX hNY
  Z evZ ZN hZ k (fun _=>True) U (ev f) (fun y hy=>Logic.I) hU x hx 0.
exact:(norm_higher_differential_unique hNX hNY hZ
  (@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD k f x hx)
  (hRestr.1 hz)).
Qed.

(** Source for [smooth_seminorm_disjoint_support_zero]: nu^i_K
    vanishes when K misses the function support, supporting
    compactness of spt T for E' in Federer 4.1.1, p. 344. *)
Theorem smooth_seminorm_disjoint_support_zero
    (K:smooth_compact_set hNX U) i (p:E->R) :
  @is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i p ->
  forall f,(forall x,smooth_compact_carrier K x -> ~support f x) -> p f=0.
Proof.
move=>hp f hf; apply/eqP; rewrite eq_le
  (smooth_derivative_seminorm_nonnegative hp f) andbT.
apply:(@smooth_derivative_seminorm_least R X Y NX NY hNX hNY U E D K i p hp f 0
  (lexx 0))=>j hj x hx.
rewrite (smooth_derivative_outside_support (smooth_compact_in_domain K x hx) (hf x hx) j)
  (real_seminorm_zero (continuous_multilinear_norm_is_norm hNY (hZ j)).1).
exact:lexx.
Qed.
End LocalSupport.
