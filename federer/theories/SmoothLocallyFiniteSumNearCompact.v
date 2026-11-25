(** Federer (1969), 4.1.1, p. 344: every
    compact neighbourhood sees a fixed finite smooth
    sum. This exact neighbourhood identity supports
    convergence of all derivatives in the common-
    support sequence proof. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  SmoothCompactSet SmoothFunctionSpaceUP NormLocallyFiniteFamilyUP FiniteFamilySumUP
  NormLocallyFiniteVectorCompactSelection SmoothFiniteSumEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_locally_finite_sum_near_compact]:
    any finite selection containing one common active
    set gives the exact smooth sum on an open
    neighbourhood of K, supporting Federer
    4.1.1, p. 344. *)
Theorem smooth_locally_finite_sum_near_compact (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (hU:forall x,U x ->norm_domain_interior NX U x)
    (E:lmodType R) (ev:E->X->Y) (hE:is_smooth_function_space hNX hNY U ev)
    (J:choiceType) (I:set J) (f:J->E) (g:E) (K:smooth_compact_set hNX U):
  is_norm_locally_finite_function_family NX U I (fun j x=>ev (f j) x) ->
  is_finite_family_sum_on U I (fun j x=>ev (f j) x) (ev g) ->
  exists (W:set X) (A:{fset J}),@open (real_norm_metric_space hNX) W /\
    smooth_compact_carrier K `<=` W /\ W `<=` U /\ (forall j,j \in A ->I j) /\
    forall F:{fset J},(forall j,j \in F ->I j) ->(A `<=` F)%fset ->
      forall x,W x ->ev g x=ev (\sum_(j<-F) f j) x.
Proof.
move=>hLocal hSum.
have hOpen:@open (real_norm_metric_space hNX) U.
  rewrite openE=>x hx.
  exact ((@norm_domain_interior_neighbourhood R X NX hNX U x).1 (hU x hx)).
have [W [A [hW [hKW [hWU [hAI hZero]]]]]]:=
  @norm_locally_finite_vector_compact_selection R X Y NX NY hNX hNY J U I (fun j x=>ev (f j) x)
    K hOpen hLocal.
exists W,A; split=>//; split=>//; split=>//; split=>// F hFI hAF x hx.
have hZeroF j (hj:I j) (hn:j \notin F):ev (f j) x=0.
  apply:(hZero x hx j hj); apply/negP=>hIn.
  have hF:(j \in F):=(fsubsetP hAF) j hIn; by move:hn; rewrite hF.
rewrite (hSum x (hWU x hx) F hFI hZeroF).
symmetry; exact:(@smooth_finite_sum_evaluation R X Y NX NY hNX hNY U E ev hE J F f x).
Qed.
