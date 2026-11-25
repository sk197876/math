(** Federer (1969), 4.1.7, p. 359:
    the actual left primitive has boundary
    delta_b. This is an interval fundamental
    theorem for every original compact scalar
    test; no primitive property is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import SmoothCompactSet CurrentEvaluation MeasureIntegralUniqueness Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialDirectional
  NormOpenDomainLaws NormClassOneUP NormClassOneLinearPostcompose
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate ExteriorGrading FiniteExteriorPowers AlternatingForms AlternatingZero
  AlternatingPairing CovectorProducts ExteriorDerivativeUP ExteriorDifferentialUP ExteriorDifferentialNormBound
  CurrentCoefficientNorms CurrentSpaces CurrentZeroCovectorMaps CurrentTestExteriorDerivative
  CurrentBoundary CurrentDensityAction CurrentDiracDensity HalflineCurrents EuclideanOneCompactPrimitiveIntegral
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP SmoothTestSpaces
  SmoothTestEvaluation SmoothGlobalFirstDifferential EuclideanLebesgueDimensions
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureIntegralUP MeasureSubsetIntegral
  RealSubsetIntegralGraph SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HalflinePrimitiveBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation Y := (A_m X R^o 0).
Local Notation NY := (@current_form_comass R h2 1 0%N).
Local Notation hNY := (@current_form_comass_real_norm R h2 1 0%N).
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation E := (@current_smooth_space R h2 1 (fun _=>True) hFull 0%N).
Local Notation ev := (@current_smooth_value R h2 1 (fun _=>True) hFull 0%N).
Local Notation hE := (@current_smooth_space_laws R h2 1 (fun _=>True) hFull 0%N).
Local Notation dE := (@current_smooth_derivatives R h2 1 (fun _=>True) hFull 0%N).
Local Notation hdE := (@current_smooth_derivative_laws R h2 1 (fun _=>True) hFull 0%N).
Local Notation value := (@current_test_value R h2 1 (fun _=>True) hFull 0%N).
Local Notation derivative := (@current_test_exterior_derivative R h2 1 0%N (fun _=>True) hFull).
Local Notation e := (@coordinate_basis R 1 ord0).
Local Notation unit := (e_lambda (@coordinate_basis R 1) (ord_tuple 1)).

(** Source for [halfline_left_primitive_boundary]:
    the first displayed whole-line primitive
    has boundary delta_b, Federer 4.1.7,
    p. 359. It is an equality
    of the actual continuous currents. *)
Theorem halfline_left_primitive_boundary b:
  @current_boundary R h2 1 0%N (fun _=>True) hFull
    (@halfline_left_primitive_candidate R h2 b)=
  @full_dirac_current R h2 1 (euclidean_one_embed b).
Proof.
apply:(@current_values_extensional R h2 1 0%N (fun _=>True) hFull)=>psi.
rewrite current_boundary_evaluation full_dirac_current_evaluation.
pose p:=smooth_test_inclusion hE psi.
pose D0:=@smooth_global_first_differential R X Y NX NY hNX hNY E dE p.
pose a:=@current_zero_form_coefficient R 1.
pose f x:=a (value psi x).
pose D x:=hom_comp a (D0 x).
have hGlobal:=@smooth_global_first_differential_class_one R X Y NX NY hNX hNY
  E ev hE dE hdE p.
have hScalar:is_norm_class_one_field NX NS (fun _=>True) f D.
  exact:(@norm_class_one_linear_postcompose R X Y R^o NX NY NS hNX hNS
    (fun _=>True) (value psi) D0 a hGlobal (@current_zero_form_coefficient_bounded R h2 1)).
have [K hK]:=smooth_test_support_bound hE psi.
have hZero:=(@smooth_function_compact_support_iff R X Y NX NY hNX hNY
  (fun _=>True) E ev hE K p).1 hK.
have hFOff x:~smooth_compact_carrier K x->f x=0.
  move=>hx.
  have hValue:value psi x=0:=@hZero x hx.
  by rewrite /f hValue linear0.
have hPair x:pairing unit
    (@current_test_value R h2 1 (fun _=>True) hFull 1%N (derivative psi) x)=D x e.
  have [L [hL hExterior]]:=@current_test_exterior_derivative_actual R h2 1 0%N
    (fun _=>True) hFull psi x Logic.I.
  have hSame:=norm_differential_unique hNX hNY hL
    (norm_class_one_differential hGlobal Logic.I).
  rewrite hSame in hExterior.
  rewrite pairing_e_lambda.
  have hTuple:[tuple of map (@coordinate_basis R 1) (ord_tuple 1)]=[tuple e].
    by apply:eq_from_tnth=>i;rewrite (ord1 i) tnth_map tnth_ord_tuple.
  rewrite hTuple hExterior exterior_differential_trace_tuple_values big_ord1 expr0 scale1r.
  rewrite (tuple0 (exterior_omitted_tuple [tuple e] ord0)).
  by rewrite /D hom_compE /a /current_zero_form_coefficient /zero_form_value /=.
have hFundamental:=@euclidean_one_compact_primitive_integral R f D K hScalar hFOff b.
pose s:=@CharacteristicFunction.value R X (@current_halfline_upper_set R b).
have hs:=@CharacteristicFunction.laws R X (@current_halfline_upper_set R b).
pose g x:=s x*D x e.
have hAction:=@halfline_left_primitive_candidate_action R h2 b (derivative psi).
have hIntegrand:(fun x=>pairing (s x*:unit)
    (@current_test_value R h2 1 (fun _=>True) hFull 1%N (derivative psi) x))=g.
  apply:funext=>x;rewrite /pairing linearZ /=.
  change (s x*pairing unit
    (@current_test_value R h2 1 (fun _=>True) hFull 1%N (derivative psi) x)=s x*D x e).
  exact:(congr1 (fun t:R=>s x*t) (@hPair x)).
rewrite hIntegrand in hAction.
have hOn:forall x,([set x:X|x ord0<=b]:set X) x->g x=D x e.
  move=>x hx;by rewrite /g /s (characteristic_on_set hs hx) mul1r.
have hOff:forall x,~([set x:X|x ord0<=b]:set X) x->g x=0.
  move=>x hx;by rewrite /g /s (characteristic_off_set hs hx) mul0r.
have hSubset:=(@real_subset_integral_total R X (@euclidean_lebesgue_measure R 1)
  [set x:X|x ord0<=b] (fun x=>D x e) g _ hOn hOff).2 hAction.
exact:(congr1 (@fine R) (measure_integral_unique hSubset hFundamental)).
Qed.
End HalflinePrimitiveBoundary.
