(** Federer (1969), 4.1.1, p. 344: every
    compact neighbourhood sees a locally finite smooth
    sequence sum as an eventually fixed ordinary partial
    sum. The finite-family identity is exact. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP SmoothCompactSet SmoothFunctionSpaceUP
  NormLocallyFiniteFamilyUP FiniteFamilySumUP FiniteNatPrefixSet SmoothLocallyFiniteSumNearCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_locally_finite_sequence_agreement]:
    all sufficiently late ordinary partial sums agree
    with the smooth sum on one open neighbourhood
    of K, supporting the common-support argument
    in Federer 4.1.1, p. 344. *)
Theorem smooth_locally_finite_sequence_agreement (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (hU:forall x,U x ->norm_domain_interior NX U x)
    (E:lmodType R) (ev:E->X->Y) (hE:is_smooth_function_space hNX hNY U ev)
    (f:nat->E) (g:E) (K:smooth_compact_set hNX U):
  is_norm_locally_finite_function_family NX U (@setT nat) (fun j x=>ev (f j) x) ->
  is_finite_family_sum_on U (@setT nat) (fun j x=>ev (f j) x) (ev g) ->
  exists N (W:set X),@open (real_norm_metric_space hNX) W /\
    smooth_compact_carrier K `<=` W /\ forall m,(N<=m)%N ->
      forall x,W x ->ev (\sum_(j<m) f j) x=ev g x.
Proof.
move=>hLocal hSum.
have [W [A [hW [hKW [hWU [hAI hNear]]]]]]:=
  @smooth_locally_finite_sum_near_compact R X Y NX NY hNX hNY U hU E ev hE
    [the choiceType of (nat:Type)] setT f g K hLocal hSum.
pose N:=(\max_(a:A) val a).+1.
exists N,W; split=>//; split=>// m hm x hx.
have hAF:(A `<=` finite_nat_prefix_set m)%fset.
  apply/fsubsetP=>j hj; rewrite finite_nat_prefix_member.
  have hSmall:(j<N)%N.
    rewrite /N ltnS; exact:(leq_bigmax ([` hj]%fset)).
  exact:leq_trans hSmall hm.
have hValue:=hNear (finite_nat_prefix_set m) (fun _ _=>Logic.I) hAF x hx.
by rewrite finite_nat_prefix_sum in hValue.
Qed.
