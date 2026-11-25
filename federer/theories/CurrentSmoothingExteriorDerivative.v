(** Federer (1969), 4.1.18, p. 375: current
    smoothing commutes with the original boundary,
    because actual smooth and compact-test smoothing
    commute with exterior differentiation. Reuse the
    original constant-coefficient differential.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentSpaces CurrentEvaluation CurrentCoefficientNorms
  CurrentCoefficientCompleteness CurrentExteriorDifferentialMap
  SmoothCurrentExteriorDerivative CurrentTestExteriorDerivative CurrentBoundary
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothSmoothingFamilyUP
  LinearSubspaceRepresentationUP SmoothingKernelUP SmoothingDilationUP
  CurrentSmoothingOperators SmoothSmoothingFirstOrderCommutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSmoothingExteriorDerivative.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation E:=(fun j=>@current_smooth_space R h2 n Full hFull j).
Local Notation ev:=(fun j=>@current_smooth_value R h2 n Full hFull j).
Local Notation hE:=(fun j=>@current_smooth_space_laws R h2 n Full hFull j).
Local Notation DT:=(fun j=>@current_test_space R h2 n Full hFull j).
Local Notation d:=(@smooth_current_exterior_derivative R h2 n m Full hFull).
Local Notation td:=(@current_test_exterior_derivative R h2 n m Full hFull).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Local Notation P:=(fun j=>@current_smooth_smoothing R h2 n j phi family hPhi hFamily).
Local Notation Q:=(fun j=>@current_test_smoothing R h2 n j phi family hPhi hFamily).

(** Source for [current_smooth_smoothing_exterior_derivative]:
    d(Phi_epsilon*omega)=Phi_epsilon*d omega, the
    form version underlying boundary commutation in
    Federer 4.1.18, p. 375. *)
Theorem current_smooth_smoothing_exterior_derivative epsilon:
  0<epsilon ->forall omega:E m,
    d (P m epsilon omega)= P m.+1 epsilon (d omega).
Proof.
move=>he omega.
exact:(@smooth_smoothing_first_order_commutation R n
  (A_m X R^o m) (A_m X R^o m.+1)
  (@current_form_comass R h2 n m) (@current_form_comass R h2 n m.+1)
  (@current_form_comass_real_norm R h2 n m)
  (@current_form_comass_real_norm R h2 n m.+1)
  (@current_form_complete R h2 n m) (@current_form_separable R h2 n m)
  (@current_form_complete R h2 n m.+1) (E m) (E m.+1) (ev m) (ev m.+1)
  (hE m) (hE m.+1) (@current_smooth_derivatives R h2 n Full hFull m)
  (@current_smooth_derivative_laws R h2 n Full hFull m)
  (@current_exterior_differential_map R h2 n m)
  (@current_exterior_differential_map_bounded R h2 n m)
  phi family hPhi hFamily (P m) (P m.+1)
  (fun e he=>@current_smooth_smoothing_convolution R h2 n m
    phi family hPhi hFamily e he)
  (fun e he=>@current_smooth_smoothing_convolution R h2 n m.+1
    phi family hPhi hFamily e he) epsilon he omega).
Qed.

(** Source for [current_test_smoothing_exterior_derivative]:
    the same original commutation holds in the actual
    compact test spaces, supporting 4.1.18, p. 375.
    No change of the literal test topology is made. *)
Theorem current_test_smoothing_exterior_derivative epsilon:
  0<epsilon ->forall omega:DT m,
    td (Q m epsilon omega)=Q m.+1 epsilon (td omega).
Proof.
move=>he omega.
apply:(subspace_representation_injective (smooth_test_space_laws (hE m.+1))).
rewrite current_test_exterior_derivative_inclusion
  (@current_test_smoothing_inclusion R h2 n m phi family hPhi hFamily epsilon he omega)
  (current_smooth_smoothing_exterior_derivative he).
rewrite (@current_test_smoothing_inclusion R h2 n m.+1 phi family hPhi hFamily
  epsilon he (td omega)) current_test_exterior_derivative_inclusion.
reflexivity.
Qed.

(** Source for [current_smoothing_boundary_commutation]:
    the literal boundary(T_epsilon)=(boundary T)_epsilon
    in Federer 4.1.18, p. 375. The input
    has positive degree; zero-degree boundary is not
    represented by an artificial negative index. *)
Theorem current_smoothing_boundary_commutation epsilon:
  0<epsilon ->forall T:@current_space R h2 n Full hFull m.+1,
    @current_boundary R h2 n m Full hFull
      (@current_smoothing R h2 n m.+1 phi family hPhi hFamily T epsilon)=
    @current_smoothing R h2 n m phi family hPhi hFamily
      (@current_boundary R h2 n m Full hFull T) epsilon.
Proof.
move=>he T;apply:(@current_values_extensional R h2 n m Full hFull)=>omega.
rewrite current_boundary_evaluation
  (@current_smoothing_action R h2 n m.+1 phi family hPhi hFamily T epsilon he)
  (@current_smoothing_action R h2 n m phi family hPhi hFamily
    (@current_boundary R h2 n m Full hFull T) epsilon he)
  current_boundary_evaluation current_test_smoothing_exterior_derivative //.
Qed.
End CurrentSmoothingExteriorDerivative.
