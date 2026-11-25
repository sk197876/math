(** Federer (1969), 4.1.27, p. 384:
    the original nondegenerate simplex current is
    H^m with the displayed orientation density
    zeta/|zeta| on f(C) and zero
    elsewhere. Apply the preceding full-fibre theorem
    to the actual compact summable cube field,
    using a proved global Lipschitz representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormClassOneUP InnerNorm InnerMetric HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct ExteriorGrading FiniteExteriorPowers
  CurrentDomain CurrentSpaces CurrentDensityUP CurrentDensityAction CurrentDensitySealed
  CurrentMapDifferential CurrentSimplexFrame LipschitzUP LipschitzBasic
  EuclideanFullDomainMeasure EuclideanOpenUnitCube
  CompactSummableMultivectors CompactSummableMultivectorDensity CompactSummableMultivectorAmbient
  CurrentLipschitzLebesgueActionDensity CurrentBoundedCharacteristicCurrent
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  CurrentAreaNormalisedImageSealed CurrentAreaFibreDensitySealed CurrentLipschitzHausdorffDensity
  PartialFunctionUP PartialFunctionExtensionUP CharacteristicFunctionSealed
  HausdorffMeasure MeasureUP OrientedSimplexCurrentSealed
  SimplexCubeParametrisationUP SimplexCubeParametrisationSealed
  SimplexCubeSourceCurrent SimplexCubeCurrentImage SimplexCubeLipschitzRepresentative
  SimplexCubeAreaDensityExtension SimplexCubeRepresentativeImage
  SimplexHausdorffDensityUP SimplexHausdorffDensitySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [simplex_hausdorff_current_density]: the complete
    normalized-density identity in the final
    display of 4.1.27, p. 384,
    under the original nondegeneracy interpretation.
    All local summability and current-construction
    evidence is derived internally; no ambient
    Radon property of H^m is imposed. *)
Theorem simplex_hausdorff_current_density (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n):
  is_nondegenerate_current_simplex v->
  exists hField:@is_locally_integrable_current_density R h2 n m
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (@SimplexHausdorffDensity.value R n m v),
    @OrientedSimplexCurrent.value R h2 n m v=
      @CurrentDensity.value R h2 n m
        (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
        (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
        (@current_area_hausdorff_measure_open_measurable R n m)
        (@SimplexHausdorffDensity.value R n m v) hField.
Proof.
move=>hIndependent.
pose X:=R_n R m;pose Y:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose FullX:=fun _:X=>True;pose FullY:=fun _:Y=>True.
pose hFullX:=fun (x:X) (_:True)=>norm_full_domain_interior NX x.
pose hFullY:=fun (y:Y) (_:True)=>norm_full_domain_interior NY y.
pose C:=@euclidean_open_unit_cube R m.
pose T:=@simplex_cube_source_current R h2 m.
pose hT:=@simplex_cube_source_current_flat R h2 m.
have[xi [hValues [hCurrent hSize]]]:=@current_bounded_characteristic_current_exists
  R h2 m C (@simplex_cube_source_measurable R m) (@simplex_cube_source_bounded R m).
pose raw:=@compact_summable_multivector_ambient_value R h2 m m FullX hFullX xi.
have hRaw:forall x,raw x=(@CharacteristicFunction.value R X C x)*:
    e_lambda (@coordinate_basis R m) (ord_tuple m).
  move=>x.
  have hInside:=@compact_summable_multivector_ambient_inside R h2 m m FullX hFullX xi
    (@euclidean_full_domain_point R m x).
  change (raw x=@compact_summable_multivector_value R h2 m m FullX hFullX xi
    (@euclidean_full_domain_point R m x)) in hInside.
  exact:eq_trans hInside (@hValues (@euclidean_full_domain_point R m x)).
have[G [W [hW [hKW [hLip [hClass [hAgreement hDifferential]]]]]]]:=
  @simplex_cube_lipschitz_representative_exists R n m v.
have hCW:forall x,C x->W x.
  move=>x hX;apply:(@hKW x).
  exact:subset_closure hX.
pose w:=@SimplexHausdorffDensity.value R n m v.
have hExt:is_partial_function_total_extension
    (@CurrentAreaFibreDensity.value R h2 X n m G
      (@CurrentAreaNormalisedImage.value R m n G raw)) w.
  apply:(@simplex_cube_area_density_extension R h2 n m v G raw hIndependent hClass).
  - move=>x hx;exact:(@hAgreement x (@hCW x hx)).
  - move=>x hx;exact:(@hDifferential x (@hCW x hx)).
  - exact:hRaw.
have[hField hDensity]:=@current_lipschitz_hausdorff_density R h2 m n xi G hLip w hExt.
pose TXi:=@compact_summable_multivector_current R h2 m m FullX hFullX xi.
pose hTXi:=@current_lipschitz_lebesgue_action_density_flat R h2 m m FullX hFullX xi.
pose hImage:=fun (x:X) (_:True)=>Logic.I.
pose hLocal:=@metric_lipschitz_is_local R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) setT G hLip.
have hEqualCurrent:=@current_flat_lipschitz_pushforward_congruence R h2 m n m
  FullX FullY hFullX hFullY G hImage hLocal TXi T hTXi hT hCurrent.
have hRepresentative:=@simplex_cube_representative_current_image R h2 n m v G hLip
  (fun x hx=>@hAgreement x (@hKW x hx)).
have hActualImage:=eq_trans hEqualCurrent (eq_trans hRepresentative
  (@simplex_cube_current_parametrisation R h2 n m v)).
exists hField;exact:eq_trans (esym hActualImage) hDensity.
Qed.

(** Source for [simplex_hausdorff_current_action]: the literal
    Hausdorff-density action on every original compact
    test in 4.1.27, p. 384.
    This is the public action of the
    actual sealed density current, not just
    equality of a mass or support bound. *)
Theorem simplex_hausdorff_current_action (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n):
  is_nondegenerate_current_simplex v->
  @is_current_density_action R h2 n m
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (@SimplexHausdorffDensity.value R n m v)
    (@OrientedSimplexCurrent.value R h2 n m v).
Proof.
move=>hIndependent.
have[hField ->]:=@simplex_hausdorff_current_density R h2 n m v hIndependent.
exact:CurrentDensity.laws.
Qed.
