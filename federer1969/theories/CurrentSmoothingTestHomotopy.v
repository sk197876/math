(** Federer (1969), 4.1.18, p. 375: the
    original smoothing homotopy identities in the
    actual compact-test spaces. Inject into smooth
    forms and use the already proved original
    identities; no test topology is altered. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Bilinear Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentTestExteriorDerivative SmoothCurrentExteriorDerivative
  SmoothTestSpaces LinearSubspaceRepresentationUP CurrentSmoothingOperators
  CurrentSmoothingFormHomotopy CurrentSmoothingTestHomotopyUP CurrentSmoothingTestHomotopySealed
  SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothingTestHomotopy.
Variable R:realType.
Hypothesis h2:(1+1:R)!= 0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation D:=(fun d=>@current_test_space R h2 n Full hFull d).
Local Notation Inc:=(fun d=>smooth_test_inclusion (@current_smooth_space_laws R h2 n Full hFull d)).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation Q:=(fun d=>@current_test_smoothing R h2 n d phi family hPhi hFamily epsilon).
Local Notation K:=(fun d=>@CurrentSmoothingTestHomotopy.value R h2 n d
  phi family hPhi hFamily epsilon hEpsilon).
Local Notation d:=(fun j=>@current_test_exterior_derivative R h2 n j Full hFull).

(** Source for [current_smoothing_test_homotopy_positive]:
    the original positive-degree form homotopy
    holds in D itself, supporting 4.1.18,
    p. 375. All terms are actual tests. *)
Theorem current_smoothing_test_homotopy_positive j (omega:D j.+1):
  Q j.+1 omega-omega= K j.+1 (d j.+1 omega)+d j (K j omega).
Proof.
apply:(subspace_representation_injective
  (smooth_test_space_laws (@current_smooth_space_laws R h2 n Full hFull j.+1))).
change (Inc j.+1 (Q j.+1 omega-omega)=
  Inc j.+1 (K j.+1 (d j.+1 omega)+d j (K j omega))).
rewrite (Bilinear.linB (hom_linear (Inc j.+1)))
  (Bilinear.linD (hom_linear (Inc j.+1)))
  (@current_test_smoothing_inclusion R h2 n j.+1 phi family hPhi hFamily epsilon hEpsilon omega)
  (@CurrentSmoothingTestHomotopy.laws R h2 n j.+1 phi family hPhi hFamily epsilon hEpsilon
    (d j.+1 omega))
  !current_test_exterior_derivative_inclusion
  (@CurrentSmoothingTestHomotopy.laws R h2 n j phi family hPhi hFamily epsilon hEpsilon omega).
exact:current_smoothing_form_homotopy_positive.
Qed.

(** Source for [current_smoothing_test_homotopy_zero]: the
    degree-zero test identity has no artificial
    negative-degree term, supporting 4.1.18,
    p. 375, including ambient R^0. *)
Theorem current_smoothing_test_homotopy_zero (omega:D 0%N):
  Q 0%N omega-omega= K 0%N (d 0%N omega).
Proof.
apply:(subspace_representation_injective
  (smooth_test_space_laws (@current_smooth_space_laws R h2 n Full hFull 0%N))).
change (Inc 0%N (Q 0%N omega-omega)=Inc 0%N (K 0%N (d 0%N omega))).
rewrite (Bilinear.linB (hom_linear (Inc 0%N)))
  (@current_test_smoothing_inclusion R h2 n 0%N phi family hPhi hFamily epsilon hEpsilon omega)
  (@CurrentSmoothingTestHomotopy.laws R h2 n 0%N phi family hPhi hFamily epsilon hEpsilon
    (d 0%N omega)) current_test_exterior_derivative_inclusion.
exact:current_smoothing_form_homotopy_zero.
Qed.
End CurrentSmoothingTestHomotopy.
