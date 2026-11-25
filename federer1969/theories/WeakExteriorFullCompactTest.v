(** Federer (1969), 4.1.19, p. 377: the
    original weak equation may be evaluated on a
    full smooth test whose compact support lies in U.
    Restrict the actual test and transport the literal
    integral; no equation across the boundary is asserted. *)
From mathcomp Require Import boolp all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  AlternatingPairing PairingLinear CurrentDomain CurrentCoefficientNorms CurrentVectorSpaces
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothRestrictionSealed
  SmoothCurrentDivergence CurrentCompactSmoothDivergenceSupport CurrentLipschitzCompactImage
  CurrentWeakExteriorPairUP EuclideanOpenDomainMeasure EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext CompactContinuousVectorZeroExtension
  OpenSubspaceExtension OpenSubspaceTotalZeroExtension MeasureIntegralUP
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FullCompactWeakTest.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation V d := (exterior_power X d).
Local Notation VN d := (@current_vector_mass R h2 n d).
Local Notation hVN d := (@current_vector_mass_real_norm R h2 n d).
Local Notation Y d := (A_m X R^o d).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation F d := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation fv d := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation hF d := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation divF := (@smooth_current_divergence R h2 n m Full hFull).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation E d := (@current_vector_smooth_space R h2 n U hU d).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n U hU d).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Variables (phi : UT -> Y m) (psi : UT -> Y m.+1).
Local Notation extensionPhi := (@compact_vector_open_extension R XT U (Y m) phi).
Local Notation extensionPsi := (@compact_vector_open_extension R XT U (Y m.+1) psi).

(** Source for [weak_current_exterior_full_compact_test]:
    every full smooth multivector test supported
    in an original compact K inside U obeys
    the literal weak equation of Federer 4.1.19,
    p. 377, against the zero-extended fields.
    Only the integral is transported; its original
    local domain and exact divergence are preserved. *)
Theorem weak_current_exterior_full_compact_test
    (K : smooth_compact_set hNX U) (eta : F m.+1) :
  @is_weak_current_exterior_pair R h2 n m U hU phi psi ->
  @smooth_function_support R X (V m.+1) NX hNX Full (F m.+1)
    (fv m.+1) eta `<=` smooth_compact_carrier K ->
  is_measure_integral Leb (real_total_integrand (fun x =>
    pairing (fv m (divF eta) x) (extensionPhi x)+
    pairing (fv m.+1 eta x) (extensionPsi x))) 0%E.
Proof.
move=> hWeak hSupport.
pose restriction := @SmoothRestriction.operator R X (V m.+1) NX (VN m.+1)
  hNX (hVN m.+1) U Full hU (fun _ _ => Logic.I)
  (E m.+1) (F m.+1) (ev m.+1) (fv m.+1) (hE m.+1) (hF m.+1).
pose etaU := restriction eta.
have hValue (x : X) (hx : U x) : fv m.+1 eta x=ev m.+1 etaU x.
  exact: (esym (@SmoothRestriction.laws R X (V m.+1) NX (VN m.+1)
    hNX (hVN m.+1) U Full hU (fun _ _ => Logic.I)
    (E m.+1) (F m.+1) (ev m.+1) (fv m.+1) (hE m.+1) (hF m.+1)
    eta x hx)).
pose KF := @current_compact_index_in_open R n U Full K (fun _ _ => Logic.I).
have hFullSupport : @smooth_function_support R X (V m.+1) NX hNX Full
    (F m.+1) (fv m.+1) eta `<=` smooth_compact_carrier KF := hSupport.
have hOff := (smooth_function_compact_support_iff (hF m.+1) KF eta).1 hFullSupport.
have hUSupport : @smooth_function_support R X (V m.+1) NX hNX U
    (E m.+1) (ev m.+1) etaU `<=` smooth_compact_carrier K.
  apply: (smooth_function_compact_support_iff (hE m.+1) K etaU).2=> x hx.
  case: (pselect (U x))=> hUx.
  - by rewrite -(@hValue x hUx); exact: hOff.
  - exact: (smooth_function_evaluation_outside (hE m.+1) etaU hUx).
have hDivergence := @current_smooth_divergence_restriction_values R h2 n m
  U hU etaU eta hValue.
have hOriginal := hWeak etaU K hUSupport.
have hOpen : @open XT U.
  rewrite openE=> x hx.
  exact: (norm_domain_interior_neighbourhood hNX U x).1 (@hU x hx).
have hImage := @open_subspace_total_zero_extension_integral R XT U Leb
  (euclidean_lebesgue_is_measure R n)
  (@euclidean_distribution_measure_open R n U hOpen)
  (fun x : UT => pairing (ev m (div etaU) (set_val x)) (phi x)+
    pairing (ev m.+1 etaU (set_val x)) (psi x)) 0%E hOriginal.
have hFunction : @open_extension R XT U (fun x : UT =>
      pairing (ev m (div etaU) (set_val x)) (phi x)+
      pairing (ev m.+1 etaU (set_val x)) (psi x))=
    (fun x => pairing (fv m (divF eta) x) (extensionPhi x)+
      pairing (fv m.+1 eta x) (extensionPsi x)).
  apply: funext=> x; case: (pselect (U x))=> hx.
  - pose a : UT := exist _ x (mem_set hx).
    change (@open_extension R XT U (fun u : UT =>
        pairing (ev m (div etaU) (set_val u)) (phi u)+
        pairing (ev m.+1 etaU (set_val u)) (psi u)) (set_val a)=
      pairing (fv m (divF eta) (set_val a)) (extensionPhi (set_val a))+
      pairing (fv m.+1 eta (set_val a)) (extensionPsi (set_val a))).
    by rewrite open_extensionE !compact_vector_open_extension_value
      (@hValue x hx) (@hDivergence x hx).
  - rewrite (open_extension_out _ hx)
      (compact_vector_open_extension_outside _ hx)
      (compact_vector_open_extension_outside _ hx).
    change (0=pairing_right (fv m (divF eta) x) 0+
      pairing_right (fv m.+1 eta x) 0).
    by rewrite !linear0 add0r.
by rewrite hFunction in hImage.
Qed.
End FullCompactWeakTest.
