(** Federer (1969), 4.1.7, p. 356: the
    original exterior derivative on comass-normed
    real forms uses the actual exterior alternation
    of 4.1.6, pp. 352–353. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms ContinuousMultilinearUP
  ContinuousMultilinearSealed ContinuousMultilinearOne CurrentCoefficientNorms CurrentFormInducedNorm
  ExteriorDifferentialUP ExteriorDifferentialSealed ExteriorDifferentialOperator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentExteriorDifferentialMap.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation Z := (A_m X R^o m.+1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation NZ := (@current_form_comass R h2 n m.+1).
Local Notation T := (@ContinuousMultilinear.space R 1 X Y NX NY hNX hNY).
Local Notation eT := (@ContinuousMultilinear.evaluation R 1 X Y NX NY hNX hNY).
Local Notation TN := (@ContinuousMultilinear.norm R 1 X Y NX NY hNX hNY).
Local Notation hT := (@ContinuousMultilinear.laws R 1 X Y NX NY hNX hNY).
Local Notation J := (@continuous_multilinear_one_evaluation R X Y T NX NY eT TN hT).

(** Source for [current_exterior_differential_map]:
    the original alternation of the actual first
    derivative, supporting Federer 4.1.7, p. 356. *)
Definition current_exterior_differential_map:Hom T Z:=
  hom_comp (@exterior_differential_map R h2 n R^o m) J.

(** Source for [current_exterior_differential_map_values]:
    the actual coefficient map obeys the original
    signed omitted-tuple formula, supporting Federer
    4.1.7, p. 356. *)
Lemma current_exterior_differential_map_values z:
  is_exterior_differential_value (J z) (current_exterior_differential_map z).
Proof. exact:ExteriorDifferential.laws. Qed.

(** Source for [current_exterior_differential_map_bounded]:
    the original map is bounded in the actual
    comass norms, supporting Federer 4.1.7, p. 356,
    by the norm bound already proved in 4.1.6. *)
Theorem current_exterior_differential_map_bounded:
  norm_bounded_linear TN NZ current_exterior_differential_map.
Proof.
exact:(@exterior_differential_operator_bounded R h2 n R^o NX (fun c:R^o=>`|c|)
  hNX (@scalar_absolute_value_norm R) m NY NZ
  (@current_form_comass_is_induced R h2 n m)
  (@current_form_comass_is_induced R h2 n m.+1) T eT TN hT).
Qed.
End CurrentExteriorDifferentialMap.
