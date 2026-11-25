(** Federer (1969), 4.1.18, p. 374: the
    original smoothing deformation is opaque. Its
    only public law is the independent literal
    scalar-average specification; existence has been
    proved before the witness is selected. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothingKernelUP SmoothingDilationUP CurrentSmoothingDeformationUP
  CurrentSmoothingDeformationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentSmoothingDeformationSignature.
(** Source for [value]: the original H_epsilon T,
    Federer 4.1.18, p. 374. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon),
  @current_space R h2 n (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x) m->
  @current_space R h2 n (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x) (1+m)%N.
(** Source for [laws]: every original compact-test
    action is the literal fixed-z deformation
    integral, Federer 4.1.18, p. 374. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon)
  (T:@current_space R h2 n (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x) m),
  @is_current_smoothing_deformation R h2 n m family epsilon T
    (@value R h2 n m phi family hPhi hFamily epsilon hEpsilon T).
End CurrentSmoothingDeformationSignature.
Module CurrentSmoothingDeformation:CurrentSmoothingDeformationSignature.
(** Source for [value]: select only the proved
    witness, sealing its parameter-product construction,
    supporting 4.1.18, p. 374. *)
Definition value (R:realType) (h2:(1+1:R)!=0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon)
  (T:@current_space R h2 n (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x) m):=
  projT1 (cid (@current_smoothing_deformation_exists R h2 n m phi family hPhi hFamily
    epsilon hEpsilon T)).
(** Source for [laws]: the independently specified
    literal action of the selected witness,
    supporting 4.1.18, p. 374. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon)
  (T:@current_space R h2 n (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x) m):
  @is_current_smoothing_deformation R h2 n m family epsilon T
    (@value R h2 n m phi family hPhi hFamily epsilon hEpsilon T).
Proof.
exact:(projT2 (cid (@current_smoothing_deformation_exists R h2 n m phi family hPhi hFamily
  epsilon hEpsilon T))).
Qed.
End CurrentSmoothingDeformation.
Arguments CurrentSmoothingDeformation.value : clear implicits.
Arguments CurrentSmoothingDeformation.laws : clear implicits.
