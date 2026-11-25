(** Federer (1969), 4.1.13, pp. 369–370: an original
    current is recovered by restricting to a support
    neighbourhood and pushing forward by its inclusion.
    Reuse the exact support restriction and the independently
    specified pushforward action from 4.1.7, p. 359. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentProperSupport CurrentPushforwardUP CurrentPushforwardExistence
  CurrentPushforwardSealed CurrentTestNearSupportAgreement CurrentElementaryPullbacks
  CurrentOpenRestriction CurrentOpenRestrictionSupport SmoothTestSpaces
  NormBoundedLinearTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentNeighbourhoodInclusion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Variables U V:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall x,V x->norm_domain_interior NX V x.
Hypothesis hUV:forall x,U x->V x.
Hypothesis hId:norm_class_all_orders hNX hNX U (fun x:X=>x).
Variable T:@current_space R h2 n V hV m.
Hypothesis hSupport:@current_support R h2 n V hV m T `<=` U.
Local Notation S := (@current_open_restriction R h2 n m U V hU hV hUV T).
Hypothesis hProper:@is_current_proper_on_support R h2 n n m U hU V S
  (fun x:X=>x) hUV.

(** Source for [current_neighbourhood_inclusion_recovery]: the
    support-neighbourhood replacement in Federer 4.1.13,
    pp. 369–370, preserves the original current after
    inclusion. The argument uses agreement near support,
    retaining arbitrary currents and the original test topology. *)
Theorem current_neighbourhood_inclusion_recovery:
  @CurrentPushforward.value R h2 n n m U V hU hV S
    (fun x:X=>x) hUV hId hProper=T.
Proof.
apply:(@current_pushforward_unique R h2 n n m U V hU hV S
  (fun x:X=>x) hUV hId hProper).
- exact:(@CurrentPushforward.laws R h2 n n m U V hU hV S
    (fun x:X=>x) hUV hId hProper).
- move=>phi psi [W [hW [hSW [hWU hAgree]]]].
  rewrite current_open_restriction_evaluation.
  have hUOpen:@open XT U.
    rewrite openE=>x hx.
    exact:((@norm_domain_interior_neighbourhood R X NX hNX U x).1 (@hU x hx)).
  apply:(@current_test_near_support_values_equal R h2 n m V hV T
    phi (@current_open_test_extension R h2 n m U V hU hV hUV psi)
    (W `&` U) (openI hW hUOpen)).
  + move=>x hx;split;last exact:@hSupport x hx.
    apply:hSW.
    rewrite current_open_restriction_support.
    exact:conj (@hSupport x hx) hx.
  + move=>x [hWx hUx].
    rewrite current_open_test_extension_values (hAgree x hWx).
    symmetry.
    exact:(@current_identity_pullback_values R h2 n U hU m V hV hUV hId
      (smooth_test_inclusion (@current_smooth_space_laws R h2 n V hV m) phi) x hUx).
Qed.
End CurrentNeighbourhoodInclusion.
