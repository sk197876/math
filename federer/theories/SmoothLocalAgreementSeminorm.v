(** Federer (1969), 4.1.1, pp. 344–345: functions that
    agree near a compact K have identical derivatives there
    and zero difference seminorm. This supplies the exact
    cutoff replacement used by compact-support functionals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  ContinuousMultilinearSealed SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSpaceLaws
  SmoothFunctionSupport SmoothFunctionDerivativesUP SmoothDerivativeSeminormUP SmoothLocalSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LocalAgreement.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation XN := (real_norm_metric_space hNX).
Local Notation support := (@smooth_function_support R X Y NX hNX U E ev).
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.

(** Source for [smooth_support_avoids_open_zero_set]: a
    function vanishing on an open W has no support point
    there, supporting the local support arguments of Federer
    4.1.1, pp. 344–345. *)
Lemma smooth_support_avoids_open_zero_set (f:E) (W:set X):
  @open XN W ->(forall x,W x ->ev f x=0) ->
  forall x,W x ->~support f x.
Proof.
move=>hW hf x hx [hu hCl].
have hSub:[set y:XN|ev f y<>0] `<=` ~` W.
  move=>y hn hy; exact:hn (hf y hy).
have hClosed:=open_closedC hW.
have h:=@closureS XN _ _ hSub x hCl.
rewrite -((closure_id _).1 hClosed) in h; exact:h hx.
Qed.

(** Source for [smooth_local_agreement_difference_seminorm]:
    nu^i_K(f-g)=0 when f=g on a neighbourhood of K,
    supporting compact cutoff replacement in Federer
    4.1.1, pp. 344–345. The original compact and order
    remain unchanged. *)
Theorem smooth_local_agreement_difference_seminorm
    (K:smooth_compact_set hNX U) i (p:E->R)
    (hp:@is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i p)
    (W:set X) f g:
  @open XN W ->smooth_compact_carrier K `<=` W ->
  (forall x,W x ->ev f x=ev g x) ->p (f-g)=0.
Proof.
move=>hW hKW he.
apply:(@smooth_seminorm_disjoint_support_zero R X Y NX NY hNX hNY U hU E ev D hD
  K i p hp (f-g))=>x hx.
apply:(smooth_support_avoids_open_zero_set hW _ (hKW x hx))=>y hy.
have hVal:ev (f-g) y=ev f y-ev g y:=
  congr1 (fun h:X->Y=>h y) (linearB (smooth_function_values_hom hE) f g).
by rewrite hVal (he y hy) subrr.
Qed.
End LocalAgreement.
