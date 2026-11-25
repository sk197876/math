(** Federer (1969), 4.1.1, pp. 344–345: replace a smooth
    function by an actual compactly supported test function
    agreeing with it near a prescribed compact set. The
    cutoff, multiplier and corestriction witnesses remain sealed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormRegularityOperations NormBoundedLinearTopology LinearBasis ContinuousMultilinearSealed CompactSupportFunctionUP
  OpenFamilyTopologyUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology SmoothCompactCutoffUP
  SmoothCompactCutoffSealed SmoothMultiplierUP SmoothMultiplierSealed SmoothCompactMultiplier
  SmoothLocalAgreementSeminorm SmoothFunctionSupport SmoothMultiplierSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CutoffReplacement.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable n:nat.
Variable b:'I_n->X.
Hypothesis hb:is_basis b.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable K:smooth_compact_set hNX U.
Local Notation chi := (@SmoothCompactCutoff.value R X NX hNX n b hb U K hU).
Local Notation hChi := (@SmoothCompactCutoff.laws R X NX hNX n b hb U K hU).

(** Source for [smooth_cutoff_replacement_scalar_class]: the
    original compact cutoff is smooth on U, supporting the
    support arguments in Federer 4.1.1, pp. 344–345. *)
Lemma smooth_cutoff_replacement_scalar_class:
  norm_class_all_orders hNX (@scalar_absolute_value_norm R) U chi.
Proof.
move=>k.
exact:(@norm_class_open_restriction R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) (fun _=>True) U chi k
  (fun _ _=>I) hU (smooth_cutoff_class hChi k)).
Qed.
Local Notation P := (@SmoothMultiplier.operator R X Y NX NY hNX hNY U E ev hE chi
  smooth_cutoff_replacement_scalar_class).
Local Notation hP := (@SmoothMultiplier.laws R X Y NX NY hNX hNY U E ev hE chi
  smooth_cutoff_replacement_scalar_class).

(** Source for [smooth_cutoff_replacement_support_bound]: the
    actual compact support of the cutoff, contained in U,
    supporting D_K in Federer 4.1.1, pp. 344–345. *)
Definition smooth_cutoff_replacement_support_bound:smooth_compact_set hNX U:=
  @Build_smooth_compact_set R X NX hNX U
    (@real_function_support R (real_norm_metric_space hNX) chi)
    (smooth_cutoff_support_in_domain hChi) (smooth_cutoff_compact hChi).
Local Notation C := smooth_cutoff_replacement_support_bound.

(** Source for [smooth_cutoff_replacement]: the actual linear
    map E to D obtained by the compact cutoff equal to one
    near K, supporting Federer 4.1.1, pp. 344–345. *)
Definition smooth_cutoff_replacement:Hom E (smooth_test_space hE):=
  @smooth_compact_multiplier_test R X Y NX NY hNX hNY U E ev hE chi P hP C
    (fun _ hx=>hx).

(** Source for [smooth_cutoff_replacement_evaluation]: the
    resulting test function equals chi phi in E, supporting
    Federer 4.1.1, pp. 344–345. *)
Lemma smooth_cutoff_replacement_evaluation f:
  smooth_test_inclusion hE (smooth_cutoff_replacement f)= P f.
Proof. exact:smooth_compact_multiplier_test_evaluation. Qed.

(** Source for [smooth_cutoff_replacement_support_subset]:
    compact cutoff replacement shrinks the original function
    support, supporting dual support restriction in Federer
    4.1.1, pp. 344–345. *)
Theorem smooth_cutoff_replacement_support_subset f:
  @smooth_function_support R X Y NX hNX U (smooth_test_space hE)
    (fun g x=>ev (smooth_test_inclusion hE g) x) (smooth_cutoff_replacement f) `<=`
    @smooth_function_support R X Y NX hNX U E ev f.
Proof.
change (@smooth_function_support R X Y NX hNX U E ev
  (smooth_test_inclusion hE (smooth_cutoff_replacement f)) `<=`
  @smooth_function_support R X Y NX hNX U E ev f).
rewrite smooth_cutoff_replacement_evaluation.
exact (@smooth_multiplier_support_subset R X Y NX NY hNX hNY U E ev hE chi P hP f).
Qed.

(** Source for [smooth_cutoff_replacement_continuous]: cutoff
    replacement is continuous from E to Federer's final D,
    supporting the dual extension in 4.1.1, p. 345. *)
Theorem smooth_cutoff_replacement_continuous:
  open_family_continuous (smooth_function_opens hD) (smooth_test_opens hE hD)
    smooth_cutoff_replacement.
Proof.
exact:(@smooth_compact_multiplier_test_continuous R X Y NX NY hNX hNY U hU E ev hE
  D hD chi smooth_cutoff_replacement_scalar_class P hP C (fun _ hx=>hx)).
Qed.

(** Source for [smooth_cutoff_replacement_agrees_near_compact]:
    one open neighbourhood of K has exact equality with the
    original function for every phi, supporting compact-support
    dual restriction in Federer 4.1.1, pp. 344–345. *)
Theorem smooth_cutoff_replacement_agrees_near_compact:
  exists W:set X,@open (real_norm_metric_space hNX) W /\
    smooth_compact_carrier K `<=` W /\ W `<=` U /\ forall f x,W x ->
      ev (smooth_test_inclusion hE (smooth_cutoff_replacement f)) x=ev f x.
Proof.
have [V [hV [hKV hOne]]]:=smooth_cutoff_neighbourhood_plateau hChi.
pose W:=V `&` U.
have hOpenU:@open (real_norm_metric_space hNX) U.
  rewrite openE=>x hx.
  exact ((@norm_domain_interior_neighbourhood R X NX hNX U x).1 (@hU x hx)).
exists W; split; first exact:openI hV hOpenU.
split; first by move=>x hx; split; [exact:hKV x hx|exact:smooth_compact_in_domain K x hx].
split; first by move=>x [hx hu].
move=>f x [hx hu]; rewrite smooth_cutoff_replacement_evaluation (hP f hu)
  (hOne x hx) scale1r; reflexivity.
Qed.

(** Source for [smooth_cutoff_replacement_seminorm_difference]:
    the original nu^i_K of the replacement difference is
    exactly zero, supporting the injective dual restriction
    in Federer 4.1.1, p. 345. *)
Theorem smooth_cutoff_replacement_seminorm_difference i f:
  smooth_function_derivative_seminorm hD K i
    (smooth_test_inclusion hE (smooth_cutoff_replacement f)-f)=0.
Proof.
have [W [hW [hKW [hWU he]]]]:=smooth_cutoff_replacement_agrees_near_compact.
exact:(@smooth_local_agreement_difference_seminorm R X Y NX NY hNX hNY U hU E ev hE D hD
  K i (smooth_function_derivative_seminorm hD K i)
  (smooth_function_derivative_seminorm_laws hD K i) W
  (smooth_test_inclusion hE (smooth_cutoff_replacement f)) f hW hKW (he f)).
Qed.
End CutoffReplacement.
