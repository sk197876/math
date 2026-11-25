(** Federer (1969), 4.1.7, p. 356: actual
    directional derivatives of forms and currents.
    Coordinate directions give the printed D_j. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  OpenFamilyTopologyUP SmoothDirectionalDerivativeUP SmoothDirectionalDerivativeSealed
  SmoothDirectionalEvaluation SmoothTestTopology DistributionDirectionalDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDirectionalDerivative.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Variable v:X.

(** Source for [current_smooth_directional_derivative]:
    actual D_v on the original smooth forms,
    supporting Federer 4.1.7, p. 356. *)
Definition current_smooth_directional_derivative:Hom E E:=
  @SmoothDirectionalDerivative.operator R X Y NX NY hNX hNY U E ev hE D hD v.

(** Source for [current_test_directional_derivative]:
    actual D_v on the original compact tests,
    supporting Federer 4.1.7, p. 356. *)
Definition current_test_directional_derivative:
    Hom (@current_test_space R h2 n U hU m) (@current_test_space R h2 n U hU m):=
  @distribution_test_directional_derivative R X Y NX NY hNX hNY U hU E ev hE D hD v.

(** Source for [current_directional_derivative]: actual
    D_v on currents, with the original negative
    transpose convention, Federer 4.1.7, p. 356. *)
Definition current_directional_derivative:
    Hom (@current_space R h2 n U hU m) (@current_space R h2 n U hU m):=
  @distribution_directional_derivative R X Y NX NY hNX hNY U hU E ev hE D hD v.

(** Source for [current_directional_derivative_evaluation]:
    (D_v T)(psi)=-T(D_v psi), supporting the
    original product rules in Federer 4.1.7,
    p. 356, by 4.1.1, p. 346. *)
Theorem current_directional_derivative_evaluation T psi:
  @current_value R h2 n U hU m (current_directional_derivative T) psi=
    -@current_value R h2 n U hU m T (current_test_directional_derivative psi).
Proof. exact:distribution_directional_derivative_evaluation. Qed.

(** Source for [current_directional_derivative_continuous]:
    the original weak continuity of current derivatives,
    supporting Federer 4.1.7, p. 356. *)
Theorem current_directional_derivative_continuous:
  open_family_continuous (@current_weak_opens R h2 n U hU m)
    (@current_weak_opens R h2 n U hU m) current_directional_derivative.
Proof. exact:distribution_directional_derivative_continuous. Qed.
End CurrentDirectionalDerivative.
