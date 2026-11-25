(** Federer (1969), 4.1.1, p. 344: pointwise
    bounded sequences in the smooth dual have a
    common compact support. This supporting stronger
    assertion proves the printed claim for convergent
    weak sequences by their real evaluations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP NormOpenTopology SmoothCompactSet SmoothCompactExhaustionUP SmoothCompactExhaustionSealed
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology FunctionalSupportUP
  ContinuousRealDual SmoothDualCompactImage SmoothDualHumpUP SmoothDualHumpConstruction SmoothDualHumpUnbounded.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PointwiseBoundedSupport.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable d:nat.
Variable b:'I_d->X.
Hypothesis hb:is_basis b.
Variable U:X->Prop.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation EO := (smooth_function_opens hD).
Local Notation hEO := (smooth_function_topology_laws hD).1.
Local Notation ED := (@continuous_real_dual_space R E EO hEO).
Local Notation e := (@continuous_real_dual_evaluation R E EO hEO).
Local Notation Comp := (smooth_compact_set hNX U).
Local Notation support := (@smooth_functional_support R X Y NX hNX U E ev).

(** Source for [smooth_dual_pointwise_bounded_common_support]:
    a pointwise bounded sequence of actual E'
    members has all supports in one original compact
    subset of U, supporting the convergent-sequence
    assertion of Federer 4.1.1, p. 344. *)
Theorem smooth_dual_pointwise_bounded_common_support (S:nat->ED):
  (forall f:E,exists M:R,0<=M /\ forall j,`|e (S j) f|<=M) ->
  exists C:Comp,forall j,support (e (S j)) `<=` smooth_compact_carrier C.
Proof.
move=>hPointwise.
case:(pselect (exists C:Comp,forall j,support (e (S j)) `<=` smooth_compact_carrier C))=>// hNo.
apply:False_ind.
pose T j:=e (S j).
have hCont j:open_family_continuous EO (norm_open_family (@scalar_absolute_value_norm R)) (T j).
  exact:(@continuous_real_dual_member_continuous R E EO hEO (S j)).
have hChoices j:exists C:Comp,support (T j) `<=` smooth_compact_carrier C.
  exact:(@smooth_dual_support_has_compact_bound R X Y NX NY hNX hNY U hU E ev D hD (S j)).
have [Bound hBound]:=choice hChoices.
pose K:=@SmoothCompactExhaustion.value R X NX hNX d b hb U hU.
have hK:=@SmoothCompactExhaustion.laws R X NX hNX d b hb U hU.
have hEsc (C:Comp):exists j,~(support (T j) `<=` smooth_compact_carrier C).
  case:(pselect (exists j,~(support (T j) `<=` smooth_compact_carrier C)))=>// hNone.
  apply:False_ind; apply:hNo; exists C=>j.
  case:(pselect (support (T j) `<=` smooth_compact_carrier C))=>// hj.
  exact:False_ind _ (hNone (ex_intro _ j hj)).
have [f [k hH]]:=@smooth_dual_hump_exists R X Y NX NY hNX hNY d b hb U hU E ev hE D hD
  T hCont Bound hBound K hK hEsc.
have [g hG]:=@smooth_dual_hump_unbounded R X Y NX NY hNX hNY U hU E ev hE D hD T hCont f k hH.
have [M [hM hB]]:=hPointwise g.
pose n:=Num.bound M.
have hLarge:M<n%:R:=archi_boundP hM.
have hUpper:=hB (k n).
change (is_true (`|T (k n) g|<=M)) in hUpper.
rewrite (hG n) normr_nat in hUpper.
have hStep:(n%:R<=n.+1%:R :>R) by rewrite ler_nat leqnSn.
have hBad:M<M:=lt_le_trans hLarge (le_trans hStep hUpper).
by rewrite ltxx in hBad.
Qed.
End PointwiseBoundedSupport.
