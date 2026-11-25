(** Federer (1969), 4.1.7, pp. 357–359:
    restriction to an open subset is the
    original transpose of test zero extension.
    Reuse the actual distribution map of
    4.1.1, p. 345, and its public laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentEvaluation CurrentDirectionalDerivative SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothTestSpaces OpenFamilyTopologyUP TestZeroExtensionUP TestZeroExtensionSealed TestZeroExtensionLaws
  TestZeroExtensionDirectional DistributionOpenRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentOpenRestriction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variables U V:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall x,V x->norm_domain_interior NX V x.
Arguments hV : clear implicits.
Hypothesis hUV:forall x,U x->V x.
Local Notation A := (@current_smooth_space R h2 n U hU m).
Local Notation B := (@current_smooth_space R h2 n V hV m).
Local Notation av := (@current_smooth_value R h2 n U hU m).
Local Notation bv := (@current_smooth_value R h2 n V hV m).
Local Notation hA := (@current_smooth_space_laws R h2 n U hU m).
Local Notation hB := (@current_smooth_space_laws R h2 n V hV m).
Local Notation DA := (@current_smooth_derivatives R h2 n U hU m).
Local Notation DB := (@current_smooth_derivatives R h2 n V hV m).
Local Notation hDA := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation hDB := (@current_smooth_derivative_laws R h2 n V hV m).

(** Source for [current_open_test_extension]: the
    original zero extension of compact form
    tests from U to V, supporting
    Federer 4.1.7, pp. 357–359. *)
Definition current_open_test_extension:
    Hom (@current_test_space R h2 n U hU m) (@current_test_space R h2 n V hV m):=
  @TestZeroExtension.operator R X Y NX NY hNX hNY U V hV hUV A B av bv hA hB.
Local Notation P := current_open_test_extension.
Local Notation hP := (@TestZeroExtension.laws R X Y NX NY hNX hNY U V hV hUV A B av bv hA hB).

(** Source for [current_open_test_extension_values]:
    actual normalized test representatives agree
    at every point, supporting the open
    restriction in Federer 4.1.7, pp. 357–359. *)
Theorem current_open_test_extension_values psi x:
  @current_test_value R h2 n V hV m (P psi) x=
    @current_test_value R h2 n U hU m psi x.
Proof.
exact:(@test_zero_extension_value R X Y NX NY hNX hNY U V A B av bv hA hB P hP psi x).
Qed.

(** Source for [current_open_restriction]: the original
    current on V restricted to open U,
    supporting E^n restricted to U and
    proper pushforward in Federer 4.1.7,
    pp. 357–359. *)
Definition current_open_restriction:Hom (@current_space R h2 n V hV m)
    (@current_space R h2 n U hU m):=
  @distribution_open_restriction R X Y NX NY hNX hNY U V hU hV hUV
    A B av bv hA hB DA DB hDA hDB.

(** Source for [current_open_restriction_evaluation]:
    the original restriction evaluates the
    zero-extended test, supporting Federer 4.1.7,
    pp. 357–359. *)
Theorem current_open_restriction_evaluation T psi:
  @current_value R h2 n U hU m (current_open_restriction T) psi=
    @current_value R h2 n V hV m T (P psi).
Proof. exact:distribution_open_restriction_evaluation. Qed.

(** Source for [current_open_restriction_continuous]:
    restriction is continuous for the original
    weak current topologies, supporting Federer
    4.1.7, pp. 357–359. *)
Theorem current_open_restriction_continuous:
  open_family_continuous (@current_weak_opens R h2 n V hV m)
    (@current_weak_opens R h2 n U hU m) current_open_restriction.
Proof. exact:distribution_open_restriction_continuous. Qed.

(** Source for [current_open_restriction_directional]:
    the original restriction commutes with D_v,
    supporting the constancy and locality
    assertions in Federer 4.1.7, pp. 357–359. *)
Theorem current_open_restriction_directional v T:
  current_open_restriction (@current_directional_derivative R h2 n m V hV v T)=
    @current_directional_derivative R h2 n m U hU v (current_open_restriction T).
Proof.
apply:(@current_values_extensional R h2 n m U hU)=>psi.
rewrite current_open_restriction_evaluation !current_directional_derivative_evaluation
  current_open_restriction_evaluation.
congr (-@current_value R h2 n V hV m T _).
exact:esym (@test_zero_extension_directional_commutes R X Y NX NY hNX hNY
  U V hU hUV A B av bv hA hB DA DB hDA hDB P hP hV v psi).
Qed.
End CurrentOpenRestriction.
