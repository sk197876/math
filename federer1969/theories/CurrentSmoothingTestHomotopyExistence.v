(** Federer (1969), 4.1.18, p. 375: compact
    support of the actual smooth homotopy images
    gives a linear test-space corestriction. The
    old opaque subspace lift supplies only an
    existence witness for the independent inclusion
    law.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothTestSpaces SmoothTestSubspaces LinearSubspaceRepresentationUP
  LinearSubspaceLiftSealed CurrentSmoothingFormHomotopySealed
  CurrentSmoothingFormHomotopyTestRange CurrentSmoothingTestHomotopyUP
  SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSmoothingTestHomotopyExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!= 0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation E:=(fun d=>@current_smooth_space R h2 n Full hFull d).
Local Notation D:=(fun d=>@current_test_space R h2 n Full hFull d).
Local Notation hE:=(fun d=>@current_smooth_space_laws R h2 n Full hFull d).
Local Notation Inc:=(fun d=>smooth_test_inclusion (hE d)).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation K:=(@CurrentSmoothingFormHomotopy.value R h2 n m phi family
  hPhi hFamily epsilon hEpsilon).

(** Source for [current_smoothing_test_homotopy_exists]:
    the original compact-test form homotopy exists
    with its exact inclusion into the smooth
    form space, supporting 4.1.18, p. 375. *)
Theorem current_smoothing_test_homotopy_exists:
  exists H:Hom (D (1+m)%N) (D m),
    @is_current_smoothing_test_homotopy R h2 n m K H.
Proof.
pose L:=hom_comp K (Inc (1+m)%N).
have hRange:forall omega,smooth_compact_support_subspace (hE m) (L omega).
  move=>omega.
  have[beta hBeta]:=@current_smoothing_form_homotopy_test_range R h2 n m
    phi family hPhi hFamily epsilon hEpsilon omega.
  rewrite /L hom_compE -hBeta.
  exact:subspace_representation_member (smooth_test_space_laws (hE m)) beta.
exists (@LinearSubspaceLift.map R (D (1+m)%N) (D m) (E m)
  (smooth_compact_support_subspace (hE m)) (Inc m) (smooth_test_space_laws (hE m)) L hRange).
move=>omega.
exact:(@LinearSubspaceLift.evaluation R (D (1+m)%N) (D m) (E m)
  (smooth_compact_support_subspace (hE m)) (Inc m) (smooth_test_space_laws (hE m)) L hRange omega).
Qed.
End CurrentSmoothingTestHomotopyExistence.
