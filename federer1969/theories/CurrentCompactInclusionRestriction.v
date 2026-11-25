(** Federer (1969), 4.1.10, p. 364: identify the original
    compact current after its ambient inclusion and restriction back
    to U. Reuse the actual pushforward, original zero extension and
    point-current action. This also handles distinct openness proofs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentEvaluation CurrentProperSupport CurrentPushforwardSealed
  CurrentCompactSmoothValue CurrentCompactPushforwardTests CurrentElementaryPullbacks
  CurrentOpenRestriction CurrentDirac SmoothFormPullbackSealed
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothTestSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentCompactInclusionRestriction.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables U V : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Hypothesis hV : forall x, V x -> norm_domain_interior NX V x.
Hypothesis hUV : forall x, U x -> V x.

(** Source for [current_compact_inclusion_restriction]: the
    identity inclusion followed by original open restriction fixes
    every compact current, supporting the star-shaped extension in
    Federer 4.1.10, p. 364. No measure representation is assumed. *)
Theorem current_compact_inclusion_restriction j
    (T : @current_space R h2 n U hU j)
    (hCompact : @compact (real_norm_metric_space hNX) (@current_support R h2 n U hU j T))
    (hId : norm_class_all_orders hNX hNX U (fun x:X => x))
    (hProper : @is_current_proper_on_support R h2 n n j U hU V T (fun x:X => x) hUV) :
  @current_open_restriction R h2 n j U V hU hV hUV
    (@CurrentPushforward.value R h2 n n j U V hU hV T (fun x:X => x) hUV hId hProper)=T.
Proof.
apply: current_values_extensional => psi.
rewrite current_open_restriction_evaluation
  (@current_compact_pushforward_test_value R h2 n n j U V hU hV
    (fun x:X => x) hUV hId T hProper hCompact).
have hPull : @SmoothFormPullback.operator R h2 n n j U V hU hV
    (fun x:X => x) hUV hId
    (smooth_test_inclusion (@current_smooth_space_laws R h2 n V hV j)
      (@current_open_test_extension R h2 n j U V hU hV hUV psi))=
  smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU j) psi.
  apply: (smooth_function_extensional (@current_smooth_space_laws R h2 n U hU j)) => x hx.
  rewrite (@current_identity_pullback_values R h2 n U hU j V hV hUV hId _ x hx).
  change (@current_test_value R h2 n V hV j
    (@current_open_test_extension R h2 n j U V hU hV hUV psi) x=
    @current_test_value R h2 n U hU j psi x).
  exact: current_open_test_extension_values.
rewrite hPull; exact: current_compact_smooth_test_value.
Qed.

(** Source for [current_open_restriction_dirac]: restricting
    the original point current on V gives the point current on U,
    supporting T(1)delta_u in Federer 4.1.10, p. 364. Both sides
    retain their normalized value at points outside U. *)
Theorem current_open_restriction_dirac (u : X) :
  @current_open_restriction R h2 n 0%N U V hU hV hUV
    (@dirac_current R h2 n V hV u)=@dirac_current R h2 n U hU u.
Proof.
apply: current_values_extensional => psi.
by rewrite current_open_restriction_evaluation !dirac_current_evaluation
  current_open_test_extension_values.
Qed.
End CurrentCompactInclusionRestriction.
