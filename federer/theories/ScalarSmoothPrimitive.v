(** Federer (1969), 3.2.33, p. 270: a scalar
    primitive of a smooth density is smooth on its actual
    open interval domain. Only the defining derivative is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormHigherCurveDerivativeUP NormClassOneLaws
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm ContinuousMultilinearScalar
  ContinuousMultilinearOne NormHigherDifferentialUP NormHigherDifferentialFirst NormClassHigherFromDerivative
  NormRegularity NormRegularityOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_primitive_of_smooth_density_smooth]: the
    assertion that g is of class infinity in Federer
    3.2.33, p. 270. The isometric one-form coefficient
    identification turns psi into the actual first differential
    field. The already proved higher derivative recursion gives
    every class, without assuming higher derivatives of g. *)
Theorem scalar_primitive_of_smooth_density_smooth (R:realType) (A:R->Prop) (psi g:R->R):
  norm_class_all_orders (scalar_absolute_value_norm R) (scalar_absolute_value_norm R) A psi ->
  (forall t,A t ->has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) A g t
    (@scalar_coefficient_linear_map R R^o (psi t))) ->
  norm_class_all_orders (scalar_absolute_value_norm R) (scalar_absolute_value_norm R) A g.
Proof.
move=>hPsi hDerivative.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i R^o R^o N N hN hN.
pose ev i:=@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN.
pose ZN i:=@ContinuousMultilinear.norm R i R^o R^o N N hN hN.
have hZ i:is_continuous_multilinear_space N N (ev i) (ZN i).
  exact:ContinuousMultilinear.laws.
have hZero:=@norm_everywhere_differentiable_class_zero R R^o R^o N N hN A g
  (fun t=>@scalar_coefficient_linear_map R R^o (psi t)) hDerivative.
have [J [hJE [hJLeft hJNorm]]]:=@continuous_multilinear_scalar_identification R 1%N R^o (Z 1%N)
  N hN (ev 1%N) (ZN 1%N) (hZ 1%N).
have hNZ:=continuous_multilinear_norm_is_norm hN (hZ 1%N).
pose W i:=@ContinuousMultilinear.space R i R^o (Z 1%N) N (ZN 1%N) hN hNZ.
pose ew i:=@ContinuousMultilinear.evaluation R i R^o (Z 1%N) N (ZN 1%N) hN hNZ.
pose WN i:=@ContinuousMultilinear.norm R i R^o (Z 1%N) N (ZN 1%N) hN hNZ.
have hW i:is_continuous_multilinear_space N (ZN 1%N) (ew i) (WN i).
  exact:ContinuousMultilinear.laws.
pose G t:=J (psi t).
have hFirst t (ht:A t):has_norm_higher_differential N ev ZN A g 1%N t (G t).
  apply:(@norm_higher_differential_first R R^o R^o N N hN hN Z ev ZN hZ A g t (G t)).2.
  have hOp:continuous_multilinear_one_operator (hZ 1%N) (G t)=
      @scalar_coefficient_linear_map R R^o (psi t).
    apply:hom_ext=>v.
    change (ev 1%N [ffun _:'I_1=>v] (J (psi t))= v*psi t).
    rewrite (continuous_multilinear_scalar_evaluation (hZ 1%N)) hJE big_ord_recr big_ord0 /= ffunE mul1r.
    by [].
  rewrite hOp; exact:hDerivative.
have hJBound:norm_bounded_linear N (ZN 1%N) J.
  exists 1; split; first exact:ler01.
  by move=>t; rewrite hJNorm mul1r.
have hWhole t (_:True):norm_domain_interior N (fun _=>True) t.
  exists 1; split; first exact:ltr01; by move=>v hv.
move=>[|k].
- exact:((norm_class_zeroP hN hN A g).2 hZero).
- have hJClass:=@norm_class_linear R R^o (Z 1%N) N (ZN 1%N) hN hNZ
    (fun _=>True) J k hWhole hJBound.
  have hGClass:=@norm_class_compose_on R R^o R^o (Z 1%N) N N (ZN 1%N) hN hN hNZ
    A (fun _=>True) psi J k (fun t (_:A t)=>Logic.I) (hPsi k) hJClass.
  have hHigher:=@norm_class_higher_from_derivative_field R 1%N k R^o R^o N N hN hN
    Z ev ZN hZ W ew WN hW A g G hZero hFirst hGClass.
  by rewrite add1n in hHigher.
Qed.
