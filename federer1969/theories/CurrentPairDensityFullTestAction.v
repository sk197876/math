(** Federer (1969), 4.1.19, p. 377: the
    two original-U density actions agree with the
    actions of the full zero-extended field distributions
    on exact compact graph tests. Only the integral
    is transported; no point of U is chosen. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  AlternatingPairing CurrentDomain CurrentCoefficientNorms CurrentVectorSpaces
  CurrentCovectorDual SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  CompactSummableMultivectors CurrentLonePairImageUP FlatCochainRepresentationUP
  DistributionIntegralFieldUP EuclideanOpenDomainMeasure EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext CompactContinuousVectorZeroExtension
  OpenSubspaceExtension OpenSubspaceTotalZeroExtension MeasureIntegralUP
  MeasureIntegralUniqueness SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PairDensityFullTests.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y d := (A_m X R^o d).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation E d := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation DT d := (smooth_test_space (hE d)).
Local Notation tv d := (smooth_test_value (hE d)).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hLeb := (euclidean_lebesgue_is_measure R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R n U hU)).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation value d := (@compact_summable_multivector_value R h2 n d U hU).
Variable beta : Hom P R^o.
Variables (phi : UT -> Y m) (psi : UT -> Y m.+1).
Local Notation extensionPhi := (@compact_vector_open_extension R XT U (Y m) phi).
Local Notation extensionPsi := (@compact_vector_open_extension R XT U (Y m.+1) psi).
Variables (T : Hom (DT m) R^o) (S : Hom (DT m.+1) R^o).

(** Source for [current_pair_density_full_test_action]:
    the original beta action on a compact
    smooth graph pair is the sum of its
    two full test actions, supporting the converse
    smoothing assertion of Federer 4.1.19, p. 377.
    No continuity of phi or psi is required. *)
Theorem current_pair_density_full_test_action (v : P) (a : DT m) (b : DT m.+1) :
  @is_lone_pair_form_density R h2 n m U hU beta phi psi ->
  is_distribution_integral_action Leb (@current_covector_evaluation R n m)
    extensionPhi (tv m) T ->
  is_distribution_integral_action Leb (@current_covector_evaluation R n m.+1)
    extensionPsi (tv m.+1) S ->
  value m v.1=(fun x : UT => tv m a (set_val x)) ->
  value m.+1 v.2=(fun x : UT => tv m.+1 b (set_val x)) ->
  beta v=T a+S b.
Proof.
move=> hDensity hT hS hLeft hRight.
have hBeta : beta v=beta (v.1,0)+beta (0,v.2).
  have hPair : ((v.1,0):P)+(0,v.2)=v.
    apply: injective_projections.
    - change (v.1+0=v.1); exact: addr0.
    - change (0+v.2=v.2); exact: add0r.
  exact: (eq_trans (congr1 beta (esym hPair))
    (linD (hom_linear beta) (v.1,0) (0,v.2))).
have hIntegral := @real_total_integral_add R UT mu hMu
  (fun x => pairing (value m v.1 x) (phi x))
  (fun x => pairing (value m.+1 v.2 x) (psi x))
  (beta (v.1,0)) (beta (0,v.2))
  (hDensity.2.2.1 v.1) (hDensity.2.2.2 v.2).
rewrite -hBeta hLeft hRight in hIntegral.
have hOpen : @open XT U.
  rewrite openE=> x hx.
  exact: (norm_domain_interior_neighbourhood hNX U x).1 (@hU x hx).
have hFullIntegral := @open_subspace_total_zero_extension_integral R XT U Leb hLeb
  (@euclidean_distribution_measure_open R n U hOpen)
  (fun x : UT => pairing (tv m a (set_val x)) (phi x)+
    pairing (tv m.+1 b (set_val x)) (psi x)) (beta v)%:E hIntegral.
have hFunction : @open_extension R XT U (fun x : UT =>
      pairing (tv m a (set_val x)) (phi x)+
      pairing (tv m.+1 b (set_val x)) (psi x))=
    (fun x => pairing (tv m a x) (extensionPhi x)+
      pairing (tv m.+1 b x) (extensionPsi x)).
  apply: funext=> x; case: (pselect (U x))=> hx.
  - pose p : UT := exist _ x (mem_set hx).
    change (@open_extension R XT U (fun x : UT =>
        pairing (tv m a (set_val x)) (phi x)+
        pairing (tv m.+1 b (set_val x)) (psi x)) (set_val p)=
      pairing (tv m a (set_val p)) (extensionPhi (set_val p))+
      pairing (tv m.+1 b (set_val p)) (extensionPsi (set_val p))).
    by rewrite open_extensionE !compact_vector_open_extension_value.
  - rewrite (open_extension_out _ hx)
      (compact_vector_open_extension_outside _ hx)
      (compact_vector_open_extension_outside _ hx).
    by rewrite (bil0r (@pairing_bilinear R X R^o m))
      (bil0r (@pairing_bilinear R X R^o m.+1)) add0r.
rewrite hFunction in hFullIntegral.
have hSum := @real_total_integral_add R X Leb hLeb
  (fun x => pairing (tv m a x) (extensionPhi x))
  (fun x => pairing (tv m.+1 b x) (extensionPsi x))
  (T a) (S b) (hT a) (hS b).
exact: (EFin_inj (measure_integral_unique hFullIntegral hSum)).
Qed.
End PairDensityFullTests.
