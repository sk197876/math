(** Federer (1969), 4.1.26, pp. 383–384:
    the field chi_A times the standard top
    orientation belongs to the original compact-summable
    multivector space whenever A is bounded and
    Lebesgue measurable. Use the preceding exact raw
    representative theorem; the carrier's construction
    and its choice witness remain opaque. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm InnerMetric HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorGrading FiniteExteriorPowers CurrentCoefficientNorms EuclideanTopCurrentMass CurrentDomain
  EuclideanDistributionMeasureContext EuclideanFullDomainMeasure EuclideanOpenDomainMeasure
  EuclideanLebesgueDimensions EuclideanLebesgueCompactInner MetricBoundedClosureLaws CoveringFamilyUP
  MetricDiameter MeasureUP MeasureBasic RadonMeasureUP OpenSubspaceMeasure IsotropyGroupTopology
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureCharacteristicIntegral
  MeasureVectorCharacteristicIntegral MeasureVectorIntegralUP MeasureLpMembershipUP
  MeasureLpNorm MeasurableNormedFunctionUP PartialFunctionUP PartialFunctionBasic
  PartialFunctionExtensionUP MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP
  CompactSummableFieldRepresentation CompactSummableFieldIntegral CompactSummableMultivectors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_bounded_characteristic_multivector_exists]:
    the original application of 4.1.25 to
    chi_A e_1 wedge ... wedge e_m,
    Federer 4.1.26, p. 384. The representative
    agrees at every point, and its exact L1
    size is L^m(A). Boundedness supplies compact
    closure and finite measure internally. *)
Theorem current_bounded_characteristic_multivector_exists
    (R:realType) (h2:(1+1:R)!=0) m
    (A:set (R_n R m))
    (hA:measure_measurable (@euclidean_lebesgue_measure R m) A)
    (hBound:@metric_set_bounded R
      (inner_metric_space (@euclidean_inner_productP R m)) A):
  exists xi:@compact_summable_multivector_space R h2 m m (fun _=>True)
      (fun x (_:True)=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R m)) x),
    (forall x:current_domain R m (fun _=>True),
      @compact_summable_multivector_value R h2 m m (fun _=>True)
        (fun y (_:True)=>norm_full_domain_interior
          (inner_norm (@euclidean_inner_productP R m)) y) xi x=
        (@CharacteristicFunction.value R (R_n R m) A (set_val x))*:
          e_lambda (@coordinate_basis R m) (ord_tuple m)) /\
    @compact_summable_multivector_size R h2 m m (fun _=>True)
      (fun x (_:True)=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R m)) x) xi=
      fine ((@euclidean_lebesgue_measure R m) A).
Proof.
pose X:=R_n R m.
pose N:=inner_norm (@euclidean_inner_productP R m).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose IT:=inner_metric_space (@euclidean_inner_productP R m).
pose NT:=real_norm_metric_space hN.
pose U:=fun _:X=>True.
pose hU:=fun (x:X) (_:True)=>norm_full_domain_interior N x.
pose FT:=current_domain R m U.
pose V:=exterior_power X m.
pose VN:=@current_vector_mass R h2 m m.
pose hVN:=@current_vector_mass_real_norm R h2 m m.
pose mu:=@euclidean_open_domain_measure R m U.
pose hMu:=proj1 (@euclidean_open_domain_measure_laws R m U hU).
pose Leb:=@euclidean_lebesgue_measure R m.
pose hLeb:=euclidean_lebesgue_is_measure R m.
pose C:set IT:=@closure IT A.
have hC:@compact IT C:=@euclidean_bounded_closure_compact R m A hBound.
have hFinite:(Leb A< +oo)%E.
  apply:(le_lt_trans (@measure_mono R X Leb hLeb A C (fun x hx=>@subset_closure IT A x hx))).
  exact:(@radon_compact_finite R IT Leb (euclidean_lebesgue_radon R m) C hC).
pose a:=fine (Leb A).
have hFiniteNumber:Leb A \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hLeb A));exact:hFinite.
have hAValue:Leb A=a%:E by rewrite /a fineK.
pose AF:set FT:=(set_val:FT->X) @^-1` A.
have hAF:measure_measurable mu AF.
  exact:(@open_subspace_preimage_measurable R NT U Leb A hA).
have hAFValue:mu AF=a%:E.
  have hAmbient:=congr1 (fun nu:set X->\bar R=>nu A)
    (@euclidean_full_domain_measure_ambient R m).
  change (mu AF=Leb A) in hAmbient.
  by rewrite hAmbient.
pose top:=e_lambda (@coordinate_basis R m) (ord_tuple m).
pose s:=fun x:FT=>@CharacteristicFunction.value R X A (set_val x).
have hs:is_characteristic_function AF s.
  constructor.
  - move=>x hx;exact:(@characteristic_on_set R X A _ (@CharacteristicFunction.laws R X A) (set_val x) hx).
  - move=>x hx;exact:(@characteristic_off_set R X A _ (@CharacteristicFunction.laws R X A) (set_val x) hx).
pose F:=fun x:FT=>s x*:top.
pose f:=partial_function_total (fun x:FT=>(F x:real_norm_metric_space hVN)).
have hIntegral:=@measure_vector_characteristic_integral R FT V VN hVN mu hMu
  AF s a top hs hAF hAFValue.
have hMeas:is_measurable_normed_function mu f:=hIntegral.1.2.1.
have hLone:(measure_lp_norm mu VN 1 f< +oo)%E:=hIntegral.1.2.2.1.
pose embed:=@euclidean_full_domain_point R m.
have hEmbed:continuous (fun x:IT=>embed x).
  apply:(@set_type_continuous_into NT U IT embed).
  exact:(@euclidean_distribution_inner_to_norm R m).
pose K:set FT:=embed @` C.
have hK:compact K.
  apply:continuous_compact hC;exact:continuous_subspaceT hEmbed.
have hOff:forall x y,partial_function_graph f x y->~K x->y=0.
  move=>x y hxy hx;change (F x=y) in hxy;rewrite -hxy /F /s.
  have hOutside:~A (set_val x).
    move=>hAx;apply:hx;exists (set_val x).
    + exact:(@subset_closure IT A (set_val x) hAx).
    + apply:val_inj;by [].
  by rewrite (characteristic_off_set (@CharacteristicFunction.laws R X A) hOutside) scale0r.
have[xi [hExtend [_ [hSupport [_ hSize]]]]]:=
  @compact_summable_partial_field_representative R FT V VN hVN mu hMu
    f hMeas hLone K hK hOff.
have hValues:forall x:FT,@compact_summable_multivector_value R h2 m m U hU xi x=F x.
  move=>x;exact:(@hExtend x (F x) (erefl _)).
exists xi;split;first exact:hValues.
have hSizeIntegral:=@compact_summable_field_size_integral R FT V VN hVN mu hMu xi.
change (is_measure_integral mu (real_total_integrand
  (fun x:FT=>VN (@compact_summable_multivector_value R h2 m m U hU xi x)))
  (@compact_summable_multivector_size R h2 m m U hU xi)%:E) in hSizeIntegral.
have hNormValues:(fun x:FT=>VN (@compact_summable_multivector_value R h2 m m U hU xi x))=s.
  apply:funext=>x;rewrite hValues /F.
  case:(pselect (AF x))=>hx.
  - by rewrite (characteristic_on_set hs hx) scale1r /VN /top
      (@euclidean_top_current_vector_mass_one R h2 m).
  - by rewrite (characteristic_off_set hs hx) scale0r /VN (real_seminorm_zero hVN.1).
rewrite hNormValues in hSizeIntegral.
have hCharacteristic:=@measure_characteristic_integral R FT mu hMu AF s hs hAF.
rewrite hAFValue in hCharacteristic.
exact:EFin_inj (measure_integral_unique hSizeIntegral hCharacteristic).
Qed.
