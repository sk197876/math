(** Federer (1969), 4.1.7, p. 356: original
    degree-zero currents are scalar distributions.
    Use the coefficient identification A^0=R of
    1.4.1, p. 17, and its actual absolute norm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis InnerProductUP
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct AlternatingForms AlternatingZero
  CurrentCoefficientNorms ZeroDegreeCovectorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentZeroCovectorMaps.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o 0).
Local Notation NY := (@current_form_comass R h2 n 0%N).

(** Source for [current_zero_form_coefficient]: the
    original scalar value of a zero-covector,
    supporting Federer 4.1.7, p. 356. *)
Definition current_zero_form_coefficient:Hom Y R^o:=
  @HomMap R Y R^o (@zero_form_value R X R^o)
    (introT (asboolP _) (@zero_form_value_linear R X R^o)).

(** Source for [current_scalar_zero_form]: the original
    scalar as a zero-covector, supporting Federer
    4.1.7, p. 356. *)
Definition current_scalar_zero_form:Hom R^o Y:=
  @HomMap R R^o Y (@zero_form R X R^o)
    (introT (asboolP _) (@zero_form_linear R X R^o)).

(** Source for [current_zero_form_coefficient_norm]:
    exact absolute scalar norm in degree zero,
    supporting Federer 4.1.7, pp. 356–357,
    with the existing degree-zero convention. *)
Lemma current_zero_form_coefficient_norm phi:NY phi=`|current_zero_form_coefficient phi|.
Proof.
exact:(@zeroth_covector_absolute_norm R h2 X (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n) phi).
Qed.

(** Source for [current_scalar_zero_form_inverse]: the
    two original scalar identifications are inverse,
    supporting Federer 4.1.7, p. 356. *)
Lemma current_scalar_zero_form_inverse c:current_zero_form_coefficient (current_scalar_zero_form c)=c.
Proof. exact:zero_formK. Qed.

(** Source for [current_zero_form_coefficient_inverse]:
    inverse identification of every original zero-
    covector, supporting Federer 4.1.7, p. 356. *)
Lemma current_zero_form_coefficient_inverse phi:current_scalar_zero_form (current_zero_form_coefficient phi)=phi.
Proof. exact:zero_form_valueK. Qed.

(** Source for [current_zero_form_coefficient_bounded]:
    the original coefficient identification is bounded,
    supporting the scalar distribution identification
    of Federer 4.1.7, p. 356. *)
Lemma current_zero_form_coefficient_bounded:
  norm_bounded_linear NY (fun c:R^o=>`|c|) current_zero_form_coefficient.
Proof.
exists 1;split;first exact:ler01.
move=>phi;by rewrite mul1r current_zero_form_coefficient_norm.
Qed.

(** Source for [current_scalar_zero_form_bounded]: the
    inverse original coefficient identification is
    bounded, supporting Federer 4.1.7, p. 356. *)
Lemma current_scalar_zero_form_bounded:
  norm_bounded_linear (fun c:R^o=>`|c|) NY current_scalar_zero_form.
Proof.
exists 1;split;first exact:ler01.
move=>c;by rewrite mul1r current_zero_form_coefficient_norm current_scalar_zero_form_inverse.
Qed.
End CurrentZeroCovectorMaps.
