(** Federer (1969), 4.1.1, p. 345: one cutoff equal
    to one near K preserves the evaluations of every
    continuous smooth functional supported in K. This
    is the fixed-support argument behind the weak embedding. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP NormOpenTopology SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSpaceLaws
  SmoothFunctionSupport SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSpaces
  SmoothCutoffReplacement SmoothLocalAgreementSeminorm FunctionalSupportUP SmoothDualFunctionalSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothDualFixedCutoff.
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
Local Notation EO := (smooth_function_opens hD).
Local Notation support := (@smooth_function_support R X Y NX hNX U E ev).
Local Notation tsupport := (@smooth_functional_support R X Y NX hNX U E ev).
Variable K:smooth_compact_set hNX U.
Local Notation C := (@smooth_cutoff_replacement R X Y NX NY hNX hNY n b hb U hU E ev hE K).
Local Notation inc := (smooth_test_inclusion hE).

(** Source for [smooth_dual_fixed_cutoff_agreement]: for
    every T supported in K and every smooth phi,
    T(phi)=T(chi phi) with one common compact cutoff,
    supporting the fixed-K weak embedding in Federer
    4.1.1, p. 345. *)
Theorem smooth_dual_fixed_cutoff_agreement (L:Hom E R^o):
  open_family_continuous EO (norm_open_family (@scalar_absolute_value_norm R)) L ->
  tsupport L `<=` smooth_compact_carrier K ->forall f,L (inc (C f))=L f.
Proof.
move=>hL hK f.
have [W [hW [hKW [hWU hAgree]]]]:=
  @smooth_cutoff_replacement_agrees_near_compact R X Y NX NY hNX hNY n b hb U hU E ev hE K.
have hZero x (hx:W x):ev (inc (C f)-f) x=0.
  have hVal:ev (inc (C f)-f) x=ev (inc (C f)) x-ev f x:=
    congr1 (fun q:X->Y=>q x) (linearB (smooth_function_values_hom hE) (inc (C f)) f).
  by rewrite hVal (hAgree f x hx) subrr.
have hValue:L (inc (C f)-f)=0.
  apply:(@smooth_dual_disjoint_support_zero R X Y NX NY hNX hNY n b hb U hU E ev hE D hD
    L (inc (C f)-f) hL)=>x ht hp.
  exact:(@smooth_support_avoids_open_zero_set R X Y NX hNX U E ev
    (inc (C f)-f) W hW hZero x (hKW x (hK x ht)) hp).
rewrite linearB in hValue.
by apply/eqP; rewrite -subr_eq0 hValue eqxx.
Qed.
End SmoothDualFixedCutoff.
