(** Federer (1969), 4.1.7, p. 356: original
    scalar tests and zero-form tests are continuously
    identified on every open U. The proof uses the
    original A^0=R maps and the actual coefficient
    operators on Federer's literal final test spaces. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms
  CurrentZeroCovectorMaps CurrentSpaces Distributions OpenFamilyTopologyUP
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestEvaluation TestTargetOperator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentScalarTestMaps.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (A_m X R^o 0).
Local Notation NY := (@current_form_comass R h2 n 0%N).
Local Notation hNY := (@current_form_comass_real_norm R h2 n 0%N).
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (@current_smooth_space R h2 n U hU 0%N).
Local Notation ev := (@current_smooth_value R h2 n U hU 0%N).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation D := (@current_smooth_derivatives R h2 n U hU 0%N).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU 0%N).
Local Notation F := (@distribution_smooth_space R X R^o NX NS hNX hNS U hU).
Local Notation fv := (@distribution_smooth_value R X R^o NX NS hNX hNS U hU).
Local Notation hF := (@distribution_smooth_laws R X R^o NX NS hNX hNS U hU).
Local Notation G := (@distribution_smooth_derivatives R X R^o NX NS hNX hNS U hU).
Local Notation hG := (@distribution_smooth_derivative_laws R X R^o NX NS hNX hNS U hU).
Local Notation TE := (@current_test_space R h2 n U hU 0%N).
Local Notation TF := (@distribution_test_space R X R^o NX NS hNX hNS U hU).
Local Notation a := (@current_zero_form_coefficient R n).
Local Notation ha := (@current_zero_form_coefficient_bounded R h2 n).
Local Notation b := (@current_scalar_zero_form R n).
Local Notation hb := (@current_scalar_zero_form_bounded R h2 n).

(** Source for [current_scalar_test_coefficients]: the
    original scalar coefficient of an actual zero-
    form test, supporting Federer 4.1.7, p. 356. *)
Definition current_scalar_test_coefficients:Hom TE TF:=
  @test_target_operator R X Y R^o NX NY NS hNX hNY hNS U E F ev fv hE hF a ha.

(** Source for [current_zero_form_test]: the original
    scalar test as an actual zero-form test,
    supporting Federer 4.1.7, p. 356. *)
Definition current_zero_form_test:Hom TF TE:=
  @test_target_operator R X R^o Y NX NS NY hNX hNS hNY U F E fv ev hF hE b hb.

(** Source for [current_scalar_test_coefficients_values]:
    exact original scalar coefficient on U,
    supporting Federer 4.1.7, p. 356. *)
Lemma current_scalar_test_coefficients_values phi x:U x->
  smooth_test_value hF (current_scalar_test_coefficients phi) x=a (smooth_test_value hE phi x).
Proof. exact:test_target_operator_value. Qed.

(** Source for [current_zero_form_test_values]: exact
    original zero-covector values on U, supporting
    Federer 4.1.7, p. 356. *)
Lemma current_zero_form_test_values phi x:U x->
  smooth_test_value hE (current_zero_form_test phi) x=b (smooth_test_value hF phi x).
Proof. exact:test_target_operator_value. Qed.

(** Source for [current_zero_form_test_inverse]: the
    original scalar coefficient and zero-form test
    maps are inverse, supporting Federer 4.1.7,
    p. 356. *)
Lemma current_zero_form_test_inverse phi:
  current_scalar_test_coefficients (current_zero_form_test phi)=phi.
Proof.
apply:(smooth_test_values_extensional hF)=>x hx.
rewrite (current_scalar_test_coefficients_values _ hx) (current_zero_form_test_values _ hx).
exact:current_scalar_zero_form_inverse.
Qed.

(** Source for [current_scalar_test_coefficients_inverse]:
    the inverse original identification holds for
    every zero-form test, supporting Federer
    4.1.7, p. 356. *)
Lemma current_scalar_test_coefficients_inverse phi:
  current_zero_form_test (current_scalar_test_coefficients phi)=phi.
Proof.
apply:(smooth_test_values_extensional hE)=>x hx.
rewrite (current_zero_form_test_values _ hx) (current_scalar_test_coefficients_values _ hx).
exact:current_zero_form_coefficient_inverse.
Qed.

(** Source for [current_scalar_test_coefficients_continuous]:
    original scalar coefficient extraction is continuous
    on the literal final test spaces, supporting
    Federer 4.1.7, p. 356. *)
Theorem current_scalar_test_coefficients_continuous:
  open_family_continuous (@current_test_opens R h2 n U hU 0%N)
    (@distribution_test_opens R X R^o NX NS hNX hNS U hU) current_scalar_test_coefficients.
Proof.
exact:(@test_target_operator_continuous R X Y R^o NX NY NS hNX hNY hNS U E F ev fv hE hF
  D G hD hG a ha).
Qed.

(** Source for [current_zero_form_test_continuous]: the
    inverse original test map is continuous for
    Federer's literal final topology, supporting
    4.1.7, p. 356. *)
Theorem current_zero_form_test_continuous:
  open_family_continuous (@distribution_test_opens R X R^o NX NS hNX hNS U hU)
    (@current_test_opens R h2 n U hU 0%N) current_zero_form_test.
Proof.
exact:(@test_target_operator_continuous R X R^o Y NX NS NY hNX hNS hNY U F E fv ev hF hE
  G D hG hD b hb).
Qed.
End CurrentScalarTestMaps.
