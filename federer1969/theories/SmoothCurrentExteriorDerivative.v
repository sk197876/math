(** Federer (1969), 4.1.7, p. 356: the
    actual exterior derivative on the original smooth
    real forms. The operator uses the sealed first-order
    realization and the original alternation of 4.1.6. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormHigherDifferentialFirst
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  ContinuousMultilinearSealed ContinuousMultilinearOne OpenFamilyTopologyUP
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology
  CurrentCoefficientNorms CurrentSpaces CurrentExteriorDifferentialMap ExteriorDerivativeUP
  SmoothFirstOrderUP SmoothFirstOrderSealed SmoothFirstOrderContinuity SmoothFirstOrderSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothCurrentExteriorDerivative.
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
Local Notation J := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation eJ := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation JN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hJ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation L := (@current_exterior_differential_map R h2 n m).
Local Notation hL := (@current_exterior_differential_map_bounded R h2 n m).

(** Source for [smooth_current_exterior_derivative]: d on
    the actual original E^m(U), used in the boundary
    definition of Federer 4.1.7, p. 356. *)
Definition smooth_current_exterior_derivative:Hom E F:=
  @SmoothFirstOrder.operator R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF D hD L hL.
Local Notation P := smooth_current_exterior_derivative.
Local Notation hP := (@SmoothFirstOrder.laws R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF D hD L hL).

(** Source for [smooth_current_exterior_derivative_values]:
    exact alternation of the actual first derivative,
    supporting Federer 4.1.7, p. 356. *)
Lemma smooth_current_exterior_derivative_values f x:
  U x->fv (P f) x=L (@D 1%N x f).
Proof. exact:(@SmoothFirstOrder.laws R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF
  D hD L hL f x). Qed.

(** Source for [smooth_current_exterior_derivative_actual]:
    the actual smooth operator has the literal original
    exterior derivative graph on U, supporting
    Federer 4.1.7, p. 356. *)
Theorem smooth_current_exterior_derivative_actual f x:
  U x->has_exterior_derivative NX NY U (ev f) x (fv (P f) x).
Proof.
move=>hx.
exists (@continuous_multilinear_one_operator R X Y (J 1%N) NX NY
  (@eJ 1%N) (@JN 1%N) (@hJ 1%N) (@D 1%N x f)); split.
- exact:(@norm_higher_differential_first R X Y NX NY hNX hNY J eJ JN hJ U (ev f)
    x (@D 1%N x f)).1 (@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD 1%N f x hx).
- rewrite (smooth_current_exterior_derivative_values f hx).
  exact:current_exterior_differential_map_values.
Qed.

(** Source for [smooth_current_exterior_derivative_continuous]:
    d is continuous between the original smooth form
    spaces, supporting Federer 4.1.7, p. 356. *)
Theorem smooth_current_exterior_derivative_continuous:
  open_family_continuous (smooth_function_opens hD) (smooth_function_opens hG) P.
Proof.
exact:(@smooth_first_order_operator_continuous R X Y Z NX NY NZ hNX hNY hNZ
  U E F ev fv hF D G hD hG L hL P hP).
Qed.
End SmoothCurrentExteriorDerivative.
