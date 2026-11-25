(** Federer (1969), 4.1.2, p. 347: every actual
    derivative evaluation of psi(x)y is the scalar
    derivative evaluation times y. This gives the
    exact differentiated finite sums on p. 348. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormHigherCurveDerivativeUP
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed ContinuousMultilinearPostcompose
  NormHigherDifferentialUP NormHigherDifferentialPostcompose NormHigherDifferentialUnique
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ScalarVectorSmoothDerivativeValue.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation P := (fun j=>@ContinuousMultilinear.space R j X R^o NX NS hNX hNS).
Local Notation ep := (fun j=>@ContinuousMultilinear.evaluation R j X R^o NX NS hNX hNS).
Local Notation PN := (fun j=>@ContinuousMultilinear.norm R j X R^o NX NS hNX hNS).
Local Notation hP := (fun j=>@ContinuousMultilinear.laws R j X R^o NX NS hNX hNS).
Local Notation Q := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation eq := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation QN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hQ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Variable D:forall j,X->Hom E (Q j).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.

(** Source for [scalar_vector_smooth_derivative_value]: the exact
    differentiated kernel-test values in Federer 4.1.2,
    pp. 347-348. All degrees and argument families
    use their original higher differential graphs. *)
Theorem scalar_vector_smooth_derivative_value (psi:X->R) k (G:X->P k) y (f:E):
  (forall x,has_norm_higher_differential NX ep PN (fun _=>True) psi k x (G x)) ->
  (forall x,ev f x=psi x*:y) ->
  forall x (u:{ffun 'I_k->X}),
    @eq k u (@D k x f)=(@ep k u (G x))*:y.
Proof.
move=>hG hValue.
pose M:=@scalar_coefficient_linear_map R Y y.
have hM:norm_bounded_linear NS NY M.
  exists (NY y); split; first exact:real_seminorm_nonnegative hNY.1 y.
  by move=>t; rewrite (real_seminorm_scale hNY.1) mulrC.
have[K [hK hKB]]:=@continuous_multilinear_postcompose_family_exists R X R^o Y NX NS NY
  P Q ep PN eq QN hP hQ M hM.
move=>x u.
have hPost:=@norm_higher_differential_field_postcompose R X R^o Y NX NS NY hNX hNS hNY
  P Q ep PN eq QN hP hQ M K hK hKB (fun _=>True) psi k G
  (fun x _=>hG x) x Logic.I.
have hActual:=@smooth_derivative_exact R X Y NX NY hNX hNY (fun _=>True) E ev D hD k f x Logic.I.
have hFun:ev f=(fun t=>M (psi t)).
  apply:funext=>t; exact:hValue t.
rewrite hFun in hActual.
have hEqual:=@norm_higher_differential_unique R X Y NX NY hNX hNY Q eq QN hQ
  (fun _=>True) (fun t=>M (psi t)) k x (@D k x f) (K k (G x)) hActual hPost.
rewrite hEqual hK; reflexivity.
Qed.
End ScalarVectorSmoothDerivativeValue.
