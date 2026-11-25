(** Federer (1969), 4.1.23, p. 380:
    the ambient simplex and its original
    open-simplex abbreviation on the same
    full domain are the same current.
    Self-restriction fixes every current by
    its literal compact-test action. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentCoefficientNorms CurrentEvaluation CurrentOpenRestriction CurrentDomainTransport
  SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_open_restriction_identity]:
    self-restriction of the actual current
    fixes all original test evaluations,
    supporting the rectangular simplex membership
    in Federer 4.1.23, p. 380.
    Every self-inclusion proof and every
    original current is allowed. *)
Theorem current_open_restriction_identity (R : realType)
    (h2 : (1+1:R)!=0) n m (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hUU : forall x, U x -> U x) (T : @current_space R h2 n U hU m) :
  @current_open_restriction R h2 n m U U hU hU hUU T=T.
Proof.
apply: (@current_values_extensional R h2 n m U hU)=> phi.
rewrite current_open_restriction_evaluation.
apply: (congr1 (@current_value R h2 n U hU m T)).
apply: (smooth_test_values_extensional (@current_smooth_space_laws R h2 n U hU m))
  => x hx.
exact: current_open_test_extension_values.
Qed.

(** Source for [current_equal_domain_restriction_identity]:
    restriction to an equal presentation
    followed by the original domain identification
    fixes every current, supporting the
    full Cartesian rectangle action in
    Federer 4.1.23, p. 380. *)
Theorem current_equal_domain_restriction_identity (R : realType)
    (h2 : (1+1:R)!=0) n m (U V : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV : forall x, V x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V x)
    (e : U=V) (hUV : forall x, U x -> V x)
    (T : @current_space R h2 n V hV m) :
  @current_domain_transport R h2 n U hU V e hV m
    (@current_open_restriction R h2 n m U V hU hV hUV T)=T.
Proof.
subst V; have hProof : hV=hU := Prop_irrelevance _ _; subst hV.
by rewrite current_domain_transport_refl current_open_restriction_identity.
Qed.
