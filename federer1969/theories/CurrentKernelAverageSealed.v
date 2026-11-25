(** Federer (1969), 4.1.18, p. 374: opaque actual
    averaging zero-current, with only its original reflected
    scalar integral law public. All bounds are proved
    separately.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  CurrentSpaces SmoothingKernelUP SmoothingDilationUP CurrentKernelAverageUP
  CurrentKernelAverageExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentKernelAverageSignature.
(** Source for [value]: the actual reflected averaging
    zero-current supporting 4.1.18, p. 374. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) n
    (phi:R_n R n->R) (family:R->R_n R n->R),
  is_smoothing_kernel phi->is_smoothing_dilation phi family->
  forall epsilon:R,0<epsilon->@current_space R h2 n (fun _=>True)
    (fun x _=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) x) 0%N.
(** Source for [laws]: the independent original integral
    specification, 4.1.18, p. 374. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) n
    (phi:R_n R n->R) (family:R->R_n R n->R)
    (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
    (epsilon:R) (hEpsilon:0<epsilon),
  @is_current_kernel_average R h2 n (fun z=>family epsilon (-z))
    (@value R h2 n phi family hPhi hFamily epsilon hEpsilon).
End CurrentKernelAverageSignature.
Module CurrentKernelAverage:CurrentKernelAverageSignature.
(** Source for [value]: hide the separately proved
    current witness, 4.1.18, p. 374. *)
Definition value (R:realType) (h2:(1+1:R)!=0) n
    (phi:R_n R n->R) (family:R->R_n R n->R)
    (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
    (epsilon:R) (hEpsilon:0<epsilon):=
  projT1 (cid (@current_kernel_average_exists R h2 n phi family
    hPhi hFamily epsilon hEpsilon)).
(** Source for [laws]: the chosen current has the
    original scalar action, 4.1.18, p. 374. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) n
    (phi:R_n R n->R) (family:R->R_n R n->R)
    (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
    (epsilon:R) (hEpsilon:0<epsilon):
  @is_current_kernel_average R h2 n (fun z=>family epsilon (-z))
    (@value R h2 n phi family hPhi hFamily epsilon hEpsilon).
Proof.
exact:(projT2 (cid (@current_kernel_average_exists R h2 n phi family
  hPhi hFamily epsilon hEpsilon))).
Qed.
End CurrentKernelAverage.
Arguments CurrentKernelAverage.value : clear implicits.
Arguments CurrentKernelAverage.laws : clear implicits.
