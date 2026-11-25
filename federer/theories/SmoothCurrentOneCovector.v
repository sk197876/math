(** Federer (1969), 4.1.7, p. 356: fixed
    one-covector contraction on actual smooth vector
    fields. Bounded coefficient postcomposition and its
    proved derivative laws retain the original spaces. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms OneCovectorInterior
  CurrentCoefficientNorms CurrentVectorSpaces CurrentOneCovectorMap CurrentVectorDirectionalDerivative
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionDerivativesUP SmoothDirectionalDerivativeUP
  ContinuousMultilinearSealed SmoothTargetOperatorUP SmoothTargetOperatorSealed SmoothTargetOperatorDerivatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothCurrentOneCovector.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (exterior_power X p.+1).
Local Notation Z := (exterior_power X p).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_vector_mass R h2 n p.+1).
Local Notation hNY := (@current_vector_mass_real_norm R h2 n p.+1).
Local Notation NZ := (@current_vector_mass R h2 n p).
Local Notation hNZ := (@current_vector_mass_real_norm R h2 n p).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (@current_vector_smooth_space R h2 n U hU p.+1).
Local Notation F := (@current_vector_smooth_space R h2 n U hU p).
Local Notation ev := (@current_vector_smooth_value R h2 n U hU p.+1).
Local Notation fv := (@current_vector_smooth_value R h2 n U hU p).
Local Notation hE := (@current_vector_smooth_space_laws R h2 n U hU p.+1).
Local Notation hF := (@current_vector_smooth_space_laws R h2 n U hU p).
Local Notation D := (@current_vector_smooth_derivatives R h2 n U hU p.+1).
Local Notation G := (@current_vector_smooth_derivatives R h2 n U hU p).
Local Notation hD := (@current_vector_smooth_derivative_laws R h2 n U hU p.+1).
Local Notation hG := (@current_vector_smooth_derivative_laws R h2 n U hU p).
Variable alpha:A_m X R^o 1.
Local Notation L := (@current_one_covector_map R h2 n p alpha).
Local Notation hL := (@current_one_covector_map_bounded R h2 n p alpha).

(** Source for [smooth_current_one_covector]: the
    original smooth xi contracted alpha, supporting
    Federer 4.1.7, p. 356. *)
Definition smooth_current_one_covector:Hom E F:=
  @SmoothTargetOperator.operator R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF L hL.
Local Notation P := smooth_current_one_covector.
Local Notation hP := (@SmoothTargetOperator.laws R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF L hL).

(** Source for [smooth_current_one_covector_values]:
    the original pointwise contraction, supporting
    Federer 4.1.7, p. 356. *)
Lemma smooth_current_one_covector_values xi x:U x->
  fv (P xi) x=positive_one_covector_interior h2 (ev xi x) alpha.
Proof. exact:SmoothTargetOperator.laws. Qed.

(** Source for [smooth_current_one_covector_directional]:
    D_v commutes with constant coefficient
    contraction, supporting the eighth identity of
    Federer 4.1.7, p. 356. The actual
    higher derivative laws supply the equality. *)
Theorem smooth_current_one_covector_directional v xi:
  @current_vector_smooth_directional_derivative R h2 n p U hU v (P xi)=
    P (@current_vector_smooth_directional_derivative R h2 n p.+1 U hU v xi).
Proof.
have[K [hK [hKb hDeriv]]]:=@smooth_target_derivative_family_exists R X Y Z NX NY NZ
  hNX hNY hNZ U E F ev fv hE hF D G hD hG L hL P hP.
apply:(smooth_function_extensional hF)=>x hx.
rewrite (@current_vector_smooth_directional_derivative_laws R h2 n p U hU v (P xi) x hx).
rewrite (smooth_current_one_covector_values _ hx).
rewrite (@current_vector_smooth_directional_derivative_laws R h2 n p.+1 U hU v xi x hx).
rewrite (hDeriv 1%N xi x hx).
exact:hK.
Qed.
End SmoothCurrentOneCovector.
