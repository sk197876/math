(** Federer (1969), 4.1.7, pp. 357–359:
    original open restriction preserves the exact
    support of each extended test and
    vanishes inside an annihilation open set.
    These supporting locality laws reuse the
    actual test zero-extension laws of 4.1.1,
    p. 345, without a new cutoff construction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import CurrentEvaluation Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentOpenRestriction CurrentSupportGeometry FunctionalSupportUP SmoothFunctionSupport
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation
  TestZeroExtensionUP TestZeroExtensionSealed TestZeroExtensionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentOpenRestrictionLocality.
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

Local Notation P := (@current_open_test_extension R h2 n m U V hU hV hUV).
Local Notation hP := (@TestZeroExtension.laws R X Y NX NY hNX hNY U V hV hUV A B av bv hA hB).

(** Source for [current_open_test_extension_support]:
    the actual original open extension has
    exactly the same support as its
    source test, supporting locality in Federer
    4.1.7, pp. 357–359, by 4.1.1,
    p. 345. *)
Theorem current_open_test_extension_support psi:
  @current_test_support R h2 n m V hV (P psi)=
    @current_test_support R h2 n m U hU psi.
Proof.
exact:(@test_zero_extension_support R X Y NX NY hNX hNY U V hUV A B av bv hA hB P hP psi).
Qed.

(** Source for [current_open_restriction_annihilation]:
    an original current restricts to zero
    on every open subset of one
    of its annihilation regions, supporting the
    half-line support argument in Federer 4.1.7,
    p. 359. The region need not
    have compact closure. *)
Theorem current_open_restriction_annihilation
    (T:@current_space R h2 n V hV m) (W:set X):
  U `<=` W->@smooth_functional_annihilation_open R X Y NX hNX V
    (@current_test_space R h2 n V hV m) (@current_test_value R h2 n V hV m)
    (@current_value R h2 n V hV m T) W->
  @current_open_restriction R h2 n m U V hU hV hUV T=0.
Proof.
move=>hUW [hW hZero].
apply:(@current_values_extensional R h2 n m U hU)=>psi.
rewrite current_open_restriction_evaluation (linear0 (@current_value R h2 n U hU m)) hom_zeroE.
apply:(@hZero (P psi)).
change (@current_test_support R h2 n m V hV (P psi) `<=` W).
rewrite current_open_test_extension_support.
move=>x hx;exact:(hUW x hx.1).
Qed.
End CurrentOpenRestrictionLocality.
