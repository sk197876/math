(** Federer (1969), 4.1.26, pp. 383–384:
    f_#(E^m restricted to A)=E^m restricted by
    degree(f|A), with its original signed numerical
    fibre sum almost everywhere. Apply 4.1.25
    to the actual characteristic top-vector field.
    No normality, inverse, finite perimeter or
    globally defined derivative is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm InnerMetric HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentDomain CurrentDensityAction CurrentDensityUP CurrentDensitySealed
  CurrentDensityUniqueness CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAmbient CurrentLipschitzLebesgueActionDensity
  EuclideanCharacteristicCurrent EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  EuclideanHausdorffLebesgue HausdorffMeasure MetricDiameter LipschitzUP LipschitzBasic
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  CharacteristicFunctionUP CharacteristicFunctionSealed
  CurrentAreaNormalisedImageUP CurrentAreaNormalisedImageSealed
  CurrentAreaFibreSumUP CurrentAreaFibreDensityUP CurrentAreaFibreDensitySealed
  CurrentAreaFibreDensityMeasurable CurrentLipschitzHausdorffAction CurrentLipschitzHausdorffDensity
  PartialFunctionUP PartialFunctionExtensionUP MeasurableFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic CurrentBoundedCharacteristicCurrent
  CurrentBoundedCharacteristicFlat LipschitzDegreeSealed LipschitzDegreeAreaGraph
  CoveringFamilyUP
  FiniteExteriorPowers
  CurrentBoundedCharacteristicMultivector.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LipschitzDegreeCharacteristicImage.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable m:nat.
Local Notation X:=(R_n R m).
Local Notation N:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hN:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior N x).
Local Notation V:=(exterior_power X m).
Local Notation top:=(e_lambda (@coordinate_basis R m) (ord_tuple m)).
Local Notation Leb:=(@euclidean_lebesgue_measure R m).
Local Notation hLeb:=(euclidean_lebesgue_is_measure R m).
Local Notation H:=(@hausdorff_measure R
  (inner_metric_space (@euclidean_inner_productP R m)) m).
Variable f:X->X.
Hypothesis hLip:@is_metric_lipschitz R
  (inner_metric_space (@euclidean_inner_productP R m))
  (inner_metric_space (@euclidean_inner_productP R m)) setT f.
Variable A:set X.
Hypothesis hA:measure_measurable Leb A.
Hypothesis hBound:@metric_set_bounded R
  (inner_metric_space (@euclidean_inner_productP R m)) A.
Local Notation chi:=(@CharacteristicFunction.value R X A).
Local Notation d:=(@LipschitzDegree.value R m f A).
Local Notation TA:=(@euclidean_characteristic_current R h2 m A hA).
Local Notation hTA:=(@current_bounded_characteristic_flat R h2 m A hA hBound).
Local Notation hLocal:=(@metric_lipschitz_is_local R
  (real_norm_metric_space hN) (real_norm_metric_space hN) setT f hLip).
Local Notation hImage:=(fun (x:X) (_:True)=>Logic.I).
Local Notation Q:=(@CurrentFlatLipschitzPushforward.value R h2 m m m
  Full Full hFull hFull f hImage hLocal TA hTA).

(** Source for [lipschitz_degree_area_representative]:
    every original total representative of the
    partial degree gives the corresponding top-vector
    representative of the area density, the
    substitution in 4.1.26, p. 384. The
    independent graphs determine this comparison. *)
Theorem lipschitz_degree_area_representative
    (xi:@compact_summable_multivector_space R h2 m m Full hFull)
    (hValues:forall x:current_domain R m Full,
      @compact_summable_multivector_value R h2 m m Full hFull xi x=
      chi (set_val x)*:top) (r:X->R):
  is_partial_function_total_extension d r->
  is_partial_function_total_extension
    (@CurrentAreaFibreDensity.value R h2 X m m f
      (@CurrentAreaNormalisedImage.value R m m f
        (@compact_summable_multivector_ambient_value R h2 m m Full hFull xi)))
    (fun y=>r y*:top).
Proof.
move=>hR.
pose raw:=@compact_summable_multivector_ambient_value R h2 m m Full hFull xi.
pose u:=@CurrentAreaNormalisedImage.value R m m f raw.
have hRaw:raw=(fun x:X=>chi x*:top).
  apply:funext=>x.
  have hInside:=@compact_summable_multivector_ambient_inside R h2 m m
    Full hFull xi (@exist X (fun z=>z \in (Full:set X)) x (mem_set (Logic.I:Full x))).
  by rewrite /raw hInside hValues.
have hU:@is_current_area_normalised_image R m m f (fun x=>chi x*:top) u.
  rewrite -hRaw;exact:(@CurrentAreaNormalisedImage.laws R m m f raw).
move=>y eta hEta.
have hSum:=(@CurrentAreaFibreDensity.laws R h2 X m m f u y eta).1 hEta.
have[hDegree hDirection]:=@area_fibre_degree_direction R h2 m f A u hU y eta hSum.
by rewrite (hR y _ hDegree) -hDirection.
Qed.

(** Source for [lipschitz_degree_conull_domain]: the
    determinant-sign sum in 4.1.26, p. 383,
    exists as a finite real value at
    Lebesgue almost every target point. The
    preceding area theorem supplies the conull
    domain; no global injectivity is assumed. *)
Theorem lipschitz_degree_conull_domain:
  measure_almost_everywhere Leb (partial_function_domain d).
Proof.
have[xi [hValues _]]:=@current_bounded_characteristic_multivector_exists
  R h2 m A hA hBound.
pose raw:=@compact_summable_multivector_ambient_value R h2 m m Full hFull xi.
pose u:=@CurrentAreaNormalisedImage.value R m m f raw.
pose eta:=@CurrentAreaFibreDensity.value R h2 X m m f u.
have hRaw:raw=(fun x:X=>chi x*:top).
  apply:funext=>x.
  have hInside:=@compact_summable_multivector_ambient_inside R h2 m m
    Full hFull xi (@exist X (fun z=>z \in (Full:set X)) x (mem_set (Logic.I:Full x))).
  by rewrite /raw hInside hValues.
have hU:@is_current_area_normalised_image R m m f (fun x=>chi x*:top) u.
  rewrite -hRaw;exact:(@CurrentAreaNormalisedImage.laws R m m f raw).
have hHL:H=Leb.
  apply:funext=>B;exact:(@euclidean_hausdorff_spherical_lebesgue R m B).1.
have hDomain:=measurable_function_domain
  (@current_area_fibre_density_measurable R h2 m m xi f hLip).
rewrite hHL in hDomain.
exact:(@area_degree_conull_domain R h2 m f A u hU Leb hLeb eta
  (@CurrentAreaFibreDensity.laws R h2 X m m f u) hDomain).
Qed.

(** Source for [lipschitz_degree_current_action]: the
    first displayed identity of 4.1.26, p. 383,
    on every original compact test. Every
    graph-preserving total degree representative gives
    this same original Lebesgue density action. *)
Theorem lipschitz_degree_current_action (r:X->R):
  is_partial_function_total_extension d r->
  @is_current_density_action R h2 m m Leb (fun y=>r y*:top) Q.
Proof.
move=>hR.
have[xi [hValues [hCurrent _]]]:=@current_bounded_characteristic_current_exists
  R h2 m A hA hBound.
have hExt:=@lipschitz_degree_area_representative xi hValues r hR.
have hAction:=@current_lipschitz_hausdorff_action R h2 m m xi f hLip
  (fun y=>r y*:top) hExt.
have hHL:H=Leb.
  apply:funext=>B;exact:(@euclidean_hausdorff_spherical_lebesgue R m B).1.
rewrite hHL in hAction.
have hEquality:=@current_flat_lipschitz_pushforward_congruence
  R h2 m m m Full Full hFull hFull f hImage hLocal
  (@compact_summable_multivector_current R h2 m m Full hFull xi) TA
  (@current_lipschitz_lebesgue_action_density_flat R h2 m m Full hFull xi)
  hTA hCurrent.
by rewrite -hEquality.
Qed.

(** Source for [lipschitz_degree_current_density]: the
    actual opaque current equality in 4.1.26,
    p. 383. Original local summability of
    the degree density is derived from the
    preceding area theorem; it is not a
    new input hypothesis. Dimension zero is retained. *)
Theorem lipschitz_degree_current_density (r:X->R):
  is_partial_function_total_extension d r->
  exists hField:@is_locally_integrable_current_density R h2 m m Leb
      (fun y=>r y*:top),
    Q=@CurrentDensity.value R h2 m m Leb hLeb
      (@euclidean_distribution_measure_open R m) (fun y=>r y*:top) hField.
Proof.
move=>hR.
have[xi [hValues _]]:=@current_bounded_characteristic_multivector_exists
  R h2 m A hA hBound.
have hExt:=@lipschitz_degree_area_representative xi hValues r hR.
have[hField _]:=@current_lipschitz_hausdorff_density R h2 m m xi f hLip
  (fun y=>r y*:top) hExt.
have hHL:H=Leb.
  apply:funext=>B;exact:(@euclidean_hausdorff_spherical_lebesgue R m B).1.
rewrite hHL in hField.
exists hField.
exact:(@current_density_action_unique R h2 m m Leb (fun y=>r y*:top) Q
  (@CurrentDensity.value R h2 m m Leb hLeb
    (@euclidean_distribution_measure_open R m) (fun y=>r y*:top) hField)
  (lipschitz_degree_current_action hR)
  (@CurrentDensity.laws R h2 m m Leb hLeb
    (@euclidean_distribution_measure_open R m) (fun y=>r y*:top) hField)).
Qed.
End LipschitzDegreeCharacteristicImage.
