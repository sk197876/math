(** Federer (1969), 4.1.23, p. 379: rotate the
    original measurable constant-vector cell before approximating
    it by coordinate rectangles. Orthogonal Lebesgue transport
    and the original smooth pullback action identify the
    actual image current. The cell may be any measurable
    subset of a compact carrier; convexity, positive measure
    and a nonzero or simple coefficient are not assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear AffineMaps RealNormUP NormMetric
  NormDifferentialUP NormDifferentialLinear NormFiniteLinearBound
  NormOpenDomainLaws NormRegularity EuclideanAffineSmooth
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct OrthogonalMaps EuclideanLinearMaps
  EuclideanLinearMeasureTransport EuclideanLinearSubsetIntegral
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  ExteriorGrading ExteriorMaps ExteriorMapScaling AlternatingForms
  AlternatingDual AlternatingPairing CurrentSpaces CurrentEvaluation CurrentCoefficientNorms
  CurrentCharacteristicDensity CurrentSupportGeometry CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardTests
  CurrentCompactSmoothValue CurrentCompactSmoothAgreement
  CurrentPushforwardDataIndependence SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionSpaceLaws SmoothTestSpaces SmoothCutoffReplacement
  SmoothFormPullbackUP SmoothFormPullbackSealed
  CompactCharacteristicCurrent CharacteristicCartesianCurrent
  PartialFunctionUP PartialFunctionPrecomposition PartialZeroExtension
  MeasureUP MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence RealSubsetIntegralAgreement
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OrthogonalCharacteristicCurrent.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation cell := (fun A hA z=>@current_characteristic_density R h2 n m
  Leb (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA z).
Local Notation E := (@current_smooth_space R h2 n Full hFull m).
Local Notation ev := (@current_smooth_value R h2 n Full hFull m).
Local Notation hE := (@current_smooth_space_laws R h2 n Full hFull m).
Local Notation value := (@current_test_value R h2 n Full hFull m).
Local Notation PN := (@current_form_comass R h2 n m).
Local Notation hPN := (@current_form_comass_real_norm R h2 n m).
Variable A : set X.
Hypothesis hA : measure_measurable Leb A.
Variable z : exterior_power X m.
Variable K : smooth_compact_set hNX Full.
Hypothesis hAK : A `<=` smooth_compact_carrier K.
Variable g : {linear X->X}.
Hypothesis hOrthogonal : is_orthogonal_map
  (@euclidean_inner_product R n) (@euclidean_inner_product R n) g.
Local Notation hf := (@euclidean_affine_map_smooth R n n Full hFull g
  (linear_affine_map g)).
Local Notation hImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation T := (cell A hA z).

(** Source for [orthogonal_characteristic_current_image_measurable]:
    the rotated cell is Lebesgue measurable, using the
    invertible linear-coordinate theorem of 2.7.16,
    pp. 134–135, in the fifth reduction of
    4.1.23, p. 379. No Borelness or
    closedness of the original measurable cell is required. *)
Lemma orthogonal_characteristic_current_image_measurable :
  measure_measurable Leb (g @` A).
Proof.
apply: (@euclidean_linear_image_measurable R n g A); last exact: hA.
exact: (@orthogonal_map_injective R X X
  (@euclidean_inner_product R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R n) g hOrthogonal).
Qed.

(** Source for [orthogonal_characteristic_current_compact]:
    the actual cell current has compact support,
    as needed for the rotation in 4.1.23,
    p. 379. Its compact carrier need not
    equal the cell or be convex. *)
Lemma orthogonal_characteristic_current_compact :
  @compact (real_norm_metric_space hNX)
    (@current_support R h2 n Full hFull m T).
Proof.
have hSupport:=(@compact_characteristic_current_properties R h2 n m A hA z K hAK).2.
exact:(@current_support_compact_bound R h2 n m Full hFull K T hSupport).
Qed.

(** Source for [orthogonal_characteristic_current_pushforward]:
    the actual orthogonal image of Lebesgue restricted
    to A wedge z is Lebesgue restricted to g(A)
    wedge Lambda_m(g)(z), supporting the fifth reduction
    of 4.1.23, p. 379. The original
    smooth image admits every compactness witness. *)
Theorem orthogonal_characteristic_current_pushforward
    (hCompact:@compact (real_norm_metric_space hNX)
      (@current_support R h2 n Full hFull m T)) :
  @current_compact_map_pushforward R h2 n n Full Full hFull hFull
    g hImage hf m T hCompact =
  cell (g @` A) orthogonal_characteristic_current_image_measurable
    (exterior_power_map g m z).
Proof.
have hSupport:=(@compact_characteristic_current_properties R h2 n m A hA z K hAK).2.
have hInjective:=@orthogonal_map_injective R X X
  (@euclidean_inner_product R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R n) g hOrthogonal.
pose L:=hom_of_linear g.
have hBounded:=@norm_finite_linear_bounded R X X NX NX hNX hNX
  n (@coordinate_basis R n) (@coordinate_basisP R n) L.
pose replace:=@smooth_cutoff_replacement R X (A_m X R^o m) NX PN hNX hPN
  n (@coordinate_basis R n) (@coordinate_basisP R n) Full hFull E ev hE K.
have [W [hW [hKW [_ hAgreement]]]]:=@smooth_cutoff_replacement_agrees_near_compact
  R X (A_m X R^o m) NX PN hNX hPN n (@coordinate_basis R n)
  (@coordinate_basisP R n) Full hFull E ev hE K.
apply:(@current_values_extensional R h2 n m Full hFull)=>phi.
pose pb:=@SmoothFormPullback.operator R h2 n n m Full Full hFull hFull
  g hImage hf (smooth_test_inclusion hE phi).
pose psi:=replace pb.
have hValue:@current_value R h2 n Full hFull m
      (@current_compact_map_pushforward R h2 n n Full Full hFull hFull
        g hImage hf m T hCompact) phi=
    @current_value R h2 n Full hFull m T psi.
  rewrite current_compact_pushforward_test_value.
  apply:(@current_compact_near_support_smooth_value R h2 n m Full hFull
    T hCompact pb psi W hW (subset_trans hSupport hKW)).
  move=>x hx;symmetry;exact:hAgreement pb x hx.
have hOriginal:=@characteristic_density_subset_action R h2 n m A hA z psi.
pose integrand:=fun y:X=>pairing (exterior_power_map g m z) (value phi y).
have hOnA x (hx:A x):pairing z (value psi x)=integrand (g x).
  have hReplacement:value psi x=ev pb x:=hAgreement pb x (@hKW x (@hAK x hx)).
  rewrite hReplacement.
  have hDifferential:=@norm_differential_linear R X X NX NX hNX hNX
    Full x L (hFull x Logic.I) hBounded.
  have hPullback:=@smooth_form_pullback_values R n n m Full Full
    E E ev ev g (@SmoothFormPullback.operator R h2 n n m Full Full hFull hFull g hImage hf)
    (@SmoothFormPullback.laws R h2 n n m Full Full hFull hFull g hImage hf)
    (smooth_test_inclusion hE phi) x L Logic.I hDifferential.
  rewrite /pb hPullback A_m_dual_pairing.
  have hMaps:forall v,hom_as_linear L v=g v by move=>v;reflexivity.
  rewrite (@exterior_power_map_ext R X X (hom_as_linear L) g hMaps m z).
  reflexivity.
have hSource:=@real_subset_integral_agreement R X Leb A
  (fun x=>pairing z (value psi x)) (fun x=>integrand (g x))
  (@current_value R h2 n Full hFull m T psi)%:E hOnA hOriginal.
have hComposition:is_measure_subset_integral Leb A
    (partial_function_precompose g (real_total_integrand integrand))
    (@current_value R h2 n Full hFull m T psi)%:E.
  apply:(@measure_integral_graph_equivalent R X Leb _ _ _ _ hSource)=>x q.
  case:(pselect (A x))=>hx.
  - by rewrite !partial_function_zero_extension_on //.
  - by rewrite !partial_function_zero_extension_off.
have hTarget:=( @euclidean_linear_subset_integral_iff R n g A
  (real_total_integrand integrand)
  (@current_value R h2 n Full hFull m T psi)%:E hInjective hA).1 hComposition.
rewrite (euclidean_orthogonal_det hOrthogonal) mul1e in hTarget.
have hActual:=@characteristic_density_subset_action R h2 n m (g @` A)
  orthogonal_characteristic_current_image_measurable (exterior_power_map g m z) phi.
rewrite hValue.
exact:EFin_inj (measure_integral_unique hTarget hActual).
Qed.

(** Source for [orthogonal_characteristic_current_pushforward_data]:
    the same actual rotation identity accepts any evidence
    of the original full-space image and smoothness laws,
    supporting 4.1.23, p. 379. These are proofs
    of already derived properties, not added mathematical
    assumptions on the orthogonal transformation. *)
Theorem orthogonal_characteristic_current_pushforward_data
    (hCompact:@compact (real_norm_metric_space hNX)
      (@current_support R h2 n Full hFull m T))
    (hMapImage:forall x,Full x->Full (g x))
    (hMapClass:norm_class_all_orders hNX hNX Full g) :
  @current_compact_map_pushforward R h2 n n Full Full hFull hFull
    g hMapImage hMapClass m T hCompact =
  cell (g @` A) orthogonal_characteristic_current_image_measurable
    (exterior_power_map g m z).
Proof.
apply:(eq_trans _ (orthogonal_characteristic_current_pushforward hCompact)).
exact:current_pushforward_data_independent.
Qed.
End OrthogonalCharacteristicCurrent.
