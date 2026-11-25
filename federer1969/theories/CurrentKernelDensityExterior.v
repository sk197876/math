(** Federer (1969), 4.1.19, p. 377: the
    exterior derivative of a smooth kernel density is
    determined by its annihilation of the translated
    divergence tests. Kernel differentiation and the original
    mass/comass duality supply the pointwise identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferentialDirectional NormOpenDomainLaws NormClassOneUP NormRegularity
  NormedCurveDerivativeUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct EuclideanCoordinateForms ExteriorGrading
  AlternatingForms AlternatingPairing PairingLinear CurrentCoefficientNorms
  CurrentVectorSpaces CurrentCovectorDual ContinuousDualUP ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestTopology
  NormOpenTopology OpenFamilyTopologyUP OneCovectorInterior CurrentOneCovectorMap
  TranslatedKernelTestUP SmoothedDistributionDensityUP SmoothedDistributionDensityExistence
  SmoothedDistributionDensityDirectional CurrentExteriorDifferentialTranspose
  ExteriorDifferentialSealed ExteriorDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section KernelDensityExterior.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NS := (fun t : R^o => `|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation V d := (exterior_power X d).
Local Notation VN d := (@current_vector_mass R h2 n d).
Local Notation hVN d := (@current_vector_mass_real_norm R h2 n d).
Local Notation Y d := (A_m X R^o d).
Local Notation YN d := (@current_form_comass R h2 n d).
Local Notation hYN d := (@current_form_comass_real_norm R h2 n d).
Local Notation ed d := (@current_covector_evaluation R n d).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation E d := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation ev d := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation D d := (@current_vector_smooth_derivatives R h2 n Full hFull d).
Local Notation hD d := (@current_vector_smooth_derivative_laws R h2 n Full hFull d).
Local Notation DT d := (smooth_test_space (hE d)).
Local Notation cut j := (@current_one_covector_map R h2 n m (euclidean_coordinate_form j)).
Variable kernel : X -> R.
Hypothesis hKernel : norm_class_all_orders hNX hNS Full kernel.
Variable radius : R.
Hypothesis hOff : forall x, radius<NX x -> kernel x=0.
Variable theta : 'I_n -> X -> R.
Variable G : 'I_n -> X -> Hom X R^o.
Hypothesis hTheta : forall j, norm_class_all_orders hNX hNS Full (theta j).
Hypothesis hThetaOff : forall j x, radius<NX x -> theta j x=0.
Hypothesis hG : forall j x, has_norm_differential NX NS Full kernel x (G j x).
Hypothesis hThetaValue : forall j x, G j x (@coordinate_basis R n j)=theta j x.
Variable B : X -> Hom (V m) (DT m).
Variable BP : X -> Hom (V m.+1) (DT m.+1).
Variable C : 'I_n -> X -> Hom (V m) (DT m).
Hypothesis hB : @is_translated_kernel_tests R X (V m) NX (VN m) hNX (hVN m)
  (E m) (ev m) (hE m) kernel B.
Hypothesis hC : forall j, @is_translated_kernel_tests R X (V m) NX (VN m)
  hNX (hVN m) (E m) (ev m) (hE m) (theta j) (C j).
Variable T : Hom (DT m) R^o.
Hypothesis hT : open_family_continuous (smooth_test_opens (hE m) (hD m))
  (norm_open_family hNS) T.
Variable S : Hom (DT m.+1) R^o.
Variables (g : X -> Y m) (h : X -> Y m.+1).
Hypothesis hDensity : is_smoothed_distribution_density B T (ed m) g.
Hypothesis hDensityP : is_smoothed_distribution_density BP S (ed m.+1) h.

(** Source for [current_kernel_density_exterior_from_tests]:
    the coefficient calculation in the smoothing
    criterion of Federer 4.1.19, p. 377.
    This supporting local lemma consumes only the
    exact kernel-test annihilation identity, which the
    original weak equation supplies in its consumer. *)
Theorem current_kernel_density_exterior_from_tests z :
  norm_class hNX (hYN m) Full g 1%N ->
  (forall a : V m.+1,
    (\sum_(j : 'I_n) T (C j z (cut j a)))+S (BP z a)=0) ->
  has_exterior_derivative NX (YN m) Full g z (h z).
Proof.
move=> hClass hAnn.
have [L hL] := (@norm_class_firstP R X (Y m) NX (YN m) hNX (hYN m) Full g).1 hClass.
have hActual := @norm_class_one_differential R X (Y m) NX (YN m) Full g L hL z Logic.I.
have hQExists (j : 'I_n) : exists q : X -> Y m,
    is_smoothed_distribution_density (C j) T (ed m) q.
  exact: (@smoothed_distribution_density_exists R n (V m) (VN m) (hVN m)
    (E m) (ev m) (hE m) (D m) (hD m) (theta j) (@hTheta j)
    radius (@hThetaOff j) (C j) (@hC j) T hT (Y m) (ed m) (YN m)
    (@current_covector_continuous_dual R h2 n m)).
have [q hQ] := choice hQExists.
have hDirectional (j : 'I_n) : L z (@coordinate_basis R n j)= -q j z.
  have hFirst := @norm_differential_directional_limit R X (Y m) NX (YN m)
    hNX (hYN m) Full g z (L z) hActual (@coordinate_basis R n j).
  have hSecond := @smoothed_distribution_density_directional R n
    (V m) (VN m) (hVN m) (E m) (ev m) (hE m) (D m) (hD m)
    kernel hKernel radius hOff B hB T hT (Y m) (ed m) (YN m)
    (@current_covector_continuous_dual R h2 n m) g hDensity
    (@coordinate_basis R n j) (theta j) (G j) (@hG j) (@hThetaValue j)
    (@hThetaOff j) (C j) (@hC j) (q j) (@hQ j) z.
  exact: (punctured_norm_limit_unique (hYN m) hFirst hSecond).
have hExterior : @ExteriorDifferential.value R h2 n R^o m (L z)=h z.
  apply: (continuous_dual_injective (@current_covector_continuous_dual R h2 n m.+1)).
  apply: hom_ext=> a.
  change (pairing a (@ExteriorDifferential.value R h2 n R^o m (L z))=pairing a (h z)).
  rewrite current_exterior_differential_transpose.
  have hTerm (j : 'I_n) :
      pairing (cut j a) (L z (@coordinate_basis R n j))= -T (C j z (cut j a)).
    rewrite hDirectional.
    change (pairing_right (cut j a) (-q j z)= -T (C j z (cut j a))).
    rewrite linearN; congr (- _).
    exact: (@hQ j z (cut j a)).
  under eq_bigr do rewrite hTerm.
  rewrite sumrN.
  have hSecondValue : pairing a (h z)=S (BP z a) := hDensityP z a.
  rewrite hSecondValue.
  have hNegative : S (BP z a)= -\sum_j T (C j z (cut j a)).
    apply: (addrI (\sum_j T (C j z (cut j a)))).
    rewrite addrN; exact: hAnn.
  exact: (esym hNegative).
exists (L z); split; first exact: hActual.
rewrite -hExterior; exact: ExteriorDifferential.laws.
Qed.
End KernelDensityExterior.
