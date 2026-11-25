(** Federer (1969), 4.1.18, p. 375: opaque
    compact-test smoothing homotopy, exposing only
    its independent exact smooth inclusion law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentSmoothingFormHomotopySealed CurrentSmoothingTestHomotopyUP
  CurrentSmoothingTestHomotopyExistence SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentSmoothingTestHomotopySignature.
(** Source for [value]: the original compact-test
    homotopy, supporting 4.1.18, p. 375. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!= 0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon),
  Hom (@current_test_space R h2 n (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x) (1+m)%N)
    (@current_test_space R h2 n (fun _=>True)
      (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x) m).
(** Source for [laws]: the actual test homotopy
    includes into the original smooth homotopy,
    supporting 4.1.18, p. 375. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!= 0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon),
  @is_current_smoothing_test_homotopy R h2 n m
    (@CurrentSmoothingFormHomotopy.value R h2 n m phi family hPhi hFamily epsilon hEpsilon)
    (@value R h2 n m phi family hPhi hFamily epsilon hEpsilon).
End CurrentSmoothingTestHomotopySignature.
Module CurrentSmoothingTestHomotopy:CurrentSmoothingTestHomotopySignature.
(** Source for [value]: choose only the proved
    test-space witness and seal its lift,
    supporting 4.1.18, p. 375. *)
Definition value (R:realType) (h2:(1+1:R)!= 0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon):=
  projT1 (cid (@current_smoothing_test_homotopy_exists R h2 n m
    phi family hPhi hFamily epsilon hEpsilon)).
(** Source for [laws]: the independent original
    inclusion law of the chosen witness,
    supporting 4.1.18, p. 375. *)
Lemma laws (R:realType) (h2:(1+1:R)!= 0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon):
  @is_current_smoothing_test_homotopy R h2 n m
    (@CurrentSmoothingFormHomotopy.value R h2 n m phi family hPhi hFamily epsilon hEpsilon)
    (@value R h2 n m phi family hPhi hFamily epsilon hEpsilon).
Proof.
exact:(projT2 (cid (@current_smoothing_test_homotopy_exists R h2 n m
  phi family hPhi hFamily epsilon hEpsilon))).
Qed.
End CurrentSmoothingTestHomotopy.
Arguments CurrentSmoothingTestHomotopy.value : clear implicits.
Arguments CurrentSmoothingTestHomotopy.laws : clear implicits.
