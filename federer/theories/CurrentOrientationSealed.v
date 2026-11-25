(** Federer (1969), 4.1.7, p. 357: the
    opaque original orienting field, specified by
    every scalar ball quotient on its exact
    maximal domain. Its existence proof is private
    to this implementation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces
  CurrentIntegrationCriterion PartialFunctionUP CurrentBallLimitsUP CurrentOrientationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentOrientationSignature.
(** Source for [value]: the original partial
    multivector field of Federer 4.1.7, p. 357. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T),
  partial_function (current_domain R n U) (exterior_power (R_n R n) m).
(** Source for [laws]: exactly the printed
    scalar-limit domain and all original covector
    pairings, Federer 4.1.7, p. 357. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T),
  @is_original_current_orienting_field R h2 n m U hU T hT (@value R h2 n m U hU T hT).
End CurrentOrientationSignature.
Module CurrentOrientation:CurrentOrientationSignature.
(** Source for [value]: hide a witness of
    the proved original orienting-field existence
    theorem, supporting Federer 4.1.7, p. 357. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T):
    partial_function (current_domain R n U) (exterior_power (R_n R n) m):=
  projT1 (cid (@original_current_orienting_field_exists R h2 n m U hU T hT)).
(** Source for [laws]: the hidden witness
    satisfies the independently specified original
    quotient laws, supporting Federer 4.1.7, p. 357. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T):
  @is_original_current_orienting_field R h2 n m U hU T hT (@value R h2 n m U hU T hT).
Proof. exact:(projT2 (cid (@original_current_orienting_field_exists R h2 n m U hU T hT))). Qed.
End CurrentOrientation.
