(** Federer (1969), 3.4.12, pp. 338–339: fixed evaluations
    of actual higher derivatives remain holomorphic. Reuse real
    analytic derivative fields, bounded evaluation, the original
    recursive derivative equation and proved higher complex linearity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  NormAnalyticLocal NormDifferentialUP NormDifferentialDirectional NormDifferentialFiniteCalculus NormAnalyticUP
  NormAnalyticLinear NormAnalyticOperations NormAnalyticHigherJet NormSmoothFields NormOpenDomainLaws
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialFields
  ComplexScalarSlotUP MultilinearSuccessorArguments MultilinearSuccessorLastReplacement HolomorphicUP HolomorphicHigherJetSlots.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Evaluation.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NY:Y->R).
Variables (hNX:is_complex_norm NX) (hNY:is_complex_norm NY).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation hNYR:=(complex_norm_real hNY).
Local Notation Z:=(fun k=>@ContinuousMultilinear.space R k XR YR NX NY hNXR hNYR).
Local Notation ev:=(fun k=>@ContinuousMultilinear.evaluation R k XR YR NX NY hNXR hNYR).
Local Notation NZ:=(fun k=>@ContinuousMultilinear.norm R k XR YR NX NY hNXR hNYR).
Local Notation hZ:=(fun k=>@ContinuousMultilinear.laws R k XR YR NX NY hNXR hNYR).

(** Source for [holomorphic_derivative_evaluation_exists]: the original
    derivative coefficients used in complex division and preparation
    are holomorphic, extending 3.4.6, pp. 322–323, as required
    by 3.4.12, p. 339. Every coefficient equation is actual. *)
Theorem holomorphic_derivative_evaluation_exists (A:set X) (f:X->Y) k (u:{ffun 'I_k->X}):
  is_holomorphic hNXR hNYR A f ->exists g:X->Y,
    (forall x,A x ->forall z:Z k,
      @has_norm_higher_differential R XR YR NX Z ev NZ A f k x z ->g x=@ev k u z) /\
    is_holomorphic hNXR hNYR A g.
Proof.
move=>hF.
have [G [hG hAnalyticG]]:=@norm_analytic_higher_jet_exists R XR YR NX NY hNXR hNYR k A f hF.1.
pose L:Hom (Z k) YR:=@ev k u.
have hL:@norm_bounded_linear R (Z k) YR (@NZ k) NY L.
  exists (\prod_(i<k) NX (u i));split.
  - apply:prodr_ge0=>i _;exact:real_seminorm_nonnegative hNXR.1 (u i).
  - move=>z;rewrite mulrC;exact:multilinear_operator_bound (continuous_multilinear_norm_laws (hZ k) z) u.
pose g:=fun x=>L (G x).
exists g;split.
- move=>x hx z hz;rewrite /g.
  by rewrite (norm_higher_differential_unique hNXR hNYR hZ (hG x hx) hz).
- split.
  + have hLinear:=@norm_bounded_linear_analytic R (Z k) YR (@NZ k) NY
      (continuous_multilinear_norm_is_norm hNYR (hZ k)) hNYR setT
      (fun z _=>norm_full_domain_interior _ z) L hL.
    exact:norm_analytic_compose_on (fun x _=>Logic.I) hAnalyticG hLinear.
  + move=>a M ha hM.
    have [D hD]:=@norm_smooth_fields_exist R XR YR NX NY hNXR hNYR A f
      (norm_analytic_class_all_orders hF.1).
    have [P [hP hStep]]:=norm_higher_differential_field_step_elim hNXR hG ((hD k.+1).1 a ha).
    have hPost:=@norm_differential_postcompose R XR (Z k) YR NX (@NZ k) NY hNXR
      A G a P L hP hL.
    have hEqual:=norm_differential_unique hNXR hNYR hM hPost.
    move=>c v;rewrite hEqual !hom_compE /L !hStep.
    have hSlots:=@holomorphic_higher_jet_scalar_slots R X Y NX NY hNX hNY
      A f hF k a (D k.+1 a) ((hD k.+1).1 a ha).
    have hScalar:=hSlots (multilinear_successor_arguments u (0:X)) ord_max c v.
    by rewrite !multilinear_successor_replace_last in hScalar.
Qed.
End Evaluation.
