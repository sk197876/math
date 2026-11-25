(** Federer (1969), 4.1.18, p. 375: the
    original smoothing form homotopy is opaque.
    Its public coefficient law is independent of
    the proved witness construction.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothingKernelUP SmoothingDilationUP CurrentSmoothingFormHomotopyUP
  CurrentSmoothingFormHomotopyExistence CurrentSmoothingFormParameterLaw.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentSmoothingFormHomotopySignature.
(** Source for [value]: the corresponding original
    form homotopy, Federer 4.1.18, p. 375. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!= 0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon),
  Hom (@current_smooth_space R h2 n (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x) (1+m)%N)
    (@current_smooth_space R h2 n (fun _=>True)
      (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x) m).
(** Source for [laws]: the original fixed-z
    scalar transgression integral on every form
    coefficient, Federer 4.1.18, p. 375. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!= 0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon),
  @is_current_smoothing_form_homotopy R h2 n m family epsilon
    (@value R h2 n m phi family hPhi hFamily epsilon hEpsilon).
(** Source for [parameter_average]: the same original
    form homotopy is the compact parameter average
    of the old opaque time transgression,
    supporting 4.1.18, p. 375. *)
Parameter parameter_average:forall (R:realType) (h2:(1+1:R)!= 0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon),
  @is_current_smoothing_form_parameter_average R h2 n m phi family hPhi hFamily epsilon hEpsilon
    (@value R h2 n m phi family hPhi hFamily epsilon hEpsilon).
End CurrentSmoothingFormHomotopySignature.
Module CurrentSmoothingFormHomotopy:CurrentSmoothingFormHomotopySignature.
(** Source for [value]: choose the proved
    original witness and hide its composition,
    supporting 4.1.18, p. 375. *)
Definition value (R:realType) (h2:(1+1:R)!= 0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon):=
  projT1 (cid (@current_smoothing_form_homotopy_exists R h2 n m
    phi family hPhi hFamily epsilon hEpsilon)).
(** Source for [laws]: the selected witness
    satisfies the independent literal coefficient
    integral, supporting 4.1.18, p. 375. *)
Lemma laws (R:realType) (h2:(1+1:R)!= 0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon):
  @is_current_smoothing_form_homotopy R h2 n m family epsilon
    (@value R h2 n m phi family hPhi hFamily epsilon hEpsilon).
Proof.
exact:(projT2 (cid (@current_smoothing_form_homotopy_exists R h2 n m
  phi family hPhi hFamily epsilon hEpsilon))).
Qed.
(** Source for [parameter_average]: derive the public
    parameter characterisation from the independent
    integral law and uniqueness, supporting
    4.1.18, p. 375. *)
Lemma parameter_average (R:realType) (h2:(1+1:R)!= 0) n m
  (phi:R_n R n->R) (family:R->R_n R n->R)
  (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
  (epsilon:R) (hEpsilon:0<epsilon):
  @is_current_smoothing_form_parameter_average R h2 n m phi family hPhi hFamily epsilon hEpsilon
    (@value R h2 n m phi family hPhi hFamily epsilon hEpsilon).
Proof.
have hEqual:@value R h2 n m phi family hPhi hFamily epsilon hEpsilon=
    @current_smoothing_form_homotopy_witness R h2 n m phi family hPhi hFamily epsilon hEpsilon.
  apply:(@current_smoothing_form_homotopy_unique R h2 n m family epsilon).
  - exact:(@laws R h2 n m phi family hPhi hFamily epsilon hEpsilon).
  - exact:(@current_smoothing_form_homotopy_witness_laws R h2 n m
      phi family hPhi hFamily epsilon hEpsilon).
move=>omega.
pose E:=fun d:nat=>@current_smooth_space R h2 n (fun _=>True)
  (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x) d.
exact:(congr1 (fun K:Hom (E ((1+m)%N)) (E m)=>K omega) hEqual).
Qed.
End CurrentSmoothingFormHomotopy.
Arguments CurrentSmoothingFormHomotopy.value : clear implicits.
Arguments CurrentSmoothingFormHomotopy.laws : clear implicits.
Arguments CurrentSmoothingFormHomotopy.parameter_average : clear implicits.
