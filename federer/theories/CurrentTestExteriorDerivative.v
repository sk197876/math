(** Federer (1969), 4.1.7, p. 356: d is
    an actual continuous operator on the original
    test forms. The fixed-support proof retains
    Federer's literal final test topology. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms OpenFamilyTopologyUP
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation
  SmoothTestTopology CurrentCoefficientNorms CurrentSpaces CurrentExteriorDifferentialMap
  SmoothCurrentExteriorDerivative SmoothFirstOrderUP SmoothFirstOrderSealed SmoothFirstOrderSupport
  SupportedSmoothOperatorTests ExteriorDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentTestExteriorDerivative.
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
Local Notation hNZ := (@current_form_comass_real_norm R h2 n m.+1).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation F := (@current_smooth_space R h2 n U hU m.+1).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation fv := (@current_smooth_value R h2 n U hU m.+1).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation hF := (@current_smooth_space_laws R h2 n U hU m.+1).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation G := (@current_smooth_derivatives R h2 n U hU m.+1).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation hG := (@current_smooth_derivative_laws R h2 n U hU m.+1).
Local Notation L := (@current_exterior_differential_map R h2 n m).
Local Notation hL := (@current_exterior_differential_map_bounded R h2 n m).
Local Notation P := (@smooth_current_exterior_derivative R h2 n m U hU).
Local Notation hP := (@SmoothFirstOrder.laws R X Y Z NX NY NZ hNX hNY hNZ
  U E F ev fv hE hF D hD L hL).
Local Notation hSupport := (@smooth_first_order_preserves_support R X Y Z NX NY NZ hNX hNY hNZ
  U hU E F ev fv hE hF D hD L P hP).

(** Source for [current_test_exterior_derivative]: d on
    the actual original D^m(U), used in the boundary
    definition of Federer 4.1.7, p. 356. *)
Definition current_test_exterior_derivative:
    Hom (@current_test_space R h2 n U hU m) (@current_test_space R h2 n U hU m.+1):=
  @supported_smooth_test_operator R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF P hSupport.

(** Source for [current_test_exterior_derivative_inclusion]:
    the original test derivative has the same smooth
    representative, supporting Federer 4.1.7, p. 356. *)
Lemma current_test_exterior_derivative_inclusion f:
  smooth_test_inclusion hF (current_test_exterior_derivative f)= P (smooth_test_inclusion hE f).
Proof. exact:supported_smooth_test_evaluation. Qed.

(** Source for [current_test_exterior_derivative_actual]:
    the actual test derivative has the original
    partial derivative graph at every point of U,
    supporting Federer 4.1.7, p. 356. *)
Theorem current_test_exterior_derivative_actual f x:
  U x->has_exterior_derivative NX NY U (@current_test_value R h2 n U hU m f) x
    (@current_test_value R h2 n U hU m.+1 (current_test_exterior_derivative f) x).
Proof.
move=>hx.
change (has_exterior_derivative NX NY U (ev (smooth_test_inclusion hE f)) x
  (fv (smooth_test_inclusion hF (current_test_exterior_derivative f)) x)).
rewrite current_test_exterior_derivative_inclusion.
exact:(@smooth_current_exterior_derivative_actual R h2 n m U hU (smooth_test_inclusion hE f) x hx).
Qed.

(** Source for [current_test_exterior_derivative_continuous]:
    d is continuous for the original literal final
    topology on test forms, supporting Federer
    4.1.7, p. 356. *)
Theorem current_test_exterior_derivative_continuous:
  open_family_continuous (@current_test_opens R h2 n U hU m)
    (@current_test_opens R h2 n U hU m.+1) current_test_exterior_derivative.
Proof.
exact:(@supported_smooth_test_continuous R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF
  D G hD hG P hSupport (@smooth_current_exterior_derivative_continuous R h2 n m U hU)).
Qed.
End CurrentTestExteriorDerivative.
