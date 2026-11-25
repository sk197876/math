(** Federer (1969), 4.1.26, p. 384: the
    original characteristic-density current is supported
    in the closure of its set. This is
    the first locality input for the displayed
    boundary-support argument. No regular boundary or
    finite perimeter is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorGrading FiniteExteriorPowers AlternatingForms AlternatingPairing PairingLinear CurrentSpaces CurrentSupportGeometry
  SmoothTestSpaces
  CurrentSupportAgreement CurrentFormSupportValues EuclideanCharacteristicCurrent
  EuclideanLebesgueDimensions MeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  MeasureSubsetIntegral SummableRealFunctionUP RealSubsetIntegralGraph
  LatticeL1ApproximationLaws
  Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_characteristic_current_support_closure]:
    spt(E^m restricted to A) is contained in
    Clos A, the original support argument of
    4.1.26, p. 384. A may be any
    Lebesgue-measurable set; boundedness is not needed
    for this supporting locality law. *)
Theorem euclidean_characteristic_current_support_closure
    (R:realType) (h2:(1+1:R)!=0) m
    (A:set (R_n R m))
    (hA:measure_measurable (@euclidean_lebesgue_measure R m) A):
  @current_support R h2 m (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) x) m
    (@euclidean_characteristic_current R h2 m A hA) `<=`
      @closure (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m))) A.
Proof.
pose X:=R_n R m.
pose N:=inner_norm (@euclidean_inner_productP R m).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose XT:=real_norm_metric_space hN.
pose U:=fun _:X=>True.
pose hU:=fun (x:X) (_:True)=>norm_full_domain_interior N x.
pose T:=@euclidean_characteristic_current R h2 m A hA.
pose W:set X:=~`(@closure XT A).
have hOpen:@open XT W:=closed_openC (@closed_closure XT A).
have hAgree:forall phi:@current_test_space R h2 m U hU m,
    @current_test_support R h2 m m U hU phi `<=` W->
    @current_value R h2 m U hU m T phi=
    @current_value R h2 m U hU m 0 phi.
  move=>phi hSupport.
  pose top:=e_lambda (@coordinate_basis R m) (ord_tuple m).
  pose k:=fun x=>pairing top (@current_test_value R h2 m U hU m phi x).
  have hZero:forall x,A x->k x=0.
    move=>x hx.
    have hOutside:~@current_test_support R h2 m m U hU phi x.
      move=>hPhi;exact:(hSupport x hPhi) (@subset_closure XT A x hx).
    have hValue:=@current_form_value_outside_support R h2 m m U hU
      (smooth_test_inclusion (@current_smooth_space_laws R h2 m U hU m) phi)
      x Logic.I hOutside.
    change (@current_test_value R h2 m U hU m phi x=0) in hValue.
    by rewrite /k hValue -pairing_rightE linear0.
  have hIntegral0:is_measure_subset_integral (@euclidean_lebesgue_measure R m) A
      (real_total_integrand k) 0%E.
    apply:(@real_subset_integral_total R X (@euclidean_lebesgue_measure R m)
      A k (fun _=>0) 0%E (fun x hx=>esym (hZero x hx)) (fun _ _=>erefl _)).2.
    exact:real_total_zero_integral (euclidean_lebesgue_is_measure R m).
  have hIntegral:=@euclidean_characteristic_current_action R h2 m A hA phi.
  have hValue:=EFin_inj (measure_integral_unique hIntegral hIntegral0).
  by rewrite hValue (lin0 (hom_linear (@current_value R h2 m U hU m))) hom_zeroE.
have hSupport:=@current_support_difference_agreement R h2 m m U hU T 0 W hOpen hAgree.
rewrite subr0 in hSupport.
move=>x hx;apply:contrapT=>hOutside.
exact:(hSupport x hx).2 hOutside.
Qed.
