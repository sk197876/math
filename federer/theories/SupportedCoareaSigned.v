(** Federer (1969), 3.2.22(3), p. 260:
    extend nonnegative supported coarea to every signed
    integrable weight, allowing either infinite integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition PartialFunctionIntegralParts PartialDensityProduct PartialZeroExtension
  MeasureUpperIntegralPositivePart MeasureUP MeasureAlmostUP MeasurableFunctionUP PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralPartsExist MeasureIntegralPartsDifference
  MeasureIntegralNegationLaw MeasureChangeOfDensity MeasureDensityUP NumericalSum NonnegativeExtendedNormOrder
  AlmostBoundedDensityIntegralComparison ParameterizedIntegral ParameterizedSubsetTotalParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [supported_coarea_signed_integral]: the
    standard approximation concluding Federer 3.2.22(3),
    p. 260, with the positive/negative-part argument
    of 3.2.12, p. 250, expanded. A bounded
    density preserves at least one finite signed
    variation. Nonnegative coarea then gives both
    signed integral graphs with exactly the same
    defined value; integrability is not strengthened
    to summability. *)
Theorem supported_coarea_signed_integral (R:realType) (X Y:choiceType)
    (rho nu beta:set X->\bar R) (alpha:set Y->\bar R)
    (hr:is_measure rho) (hn:is_measure nu) (hb:is_measure beta) (ha:is_measure alpha)
    (F:X->Y) (W:set X) (d:partial_function X (extended_real_line R))
    (u:X->extended_real_line R):
  is_measure_density rho d nu ->is_measure_measurable_function rho d ->
  measure_almost_everywhere rho (partial_extended_nonnegative_locus d) ->
  (exists C:R,(0<C)%R /\ measure_almost_everywhere rho
    [set x|forall j,partial_function_graph d x j ->j<=C%:E]) ->
  (forall v:X->extended_real_line R,
    is_measure_measurable_function rho (partial_function_total v) ->
    (forall x,0<=v x) ->(forall x,~W x ->v x=0) ->
    exists a,is_measure_integral nu (partial_function_total v) a /\
      is_measure_integral alpha (parameterized_integral beta
        (fun y=>partial_function_zero_extension (0:extended_real_line R) [set x|F x=y]
          (partial_function_total v))) a) ->
  is_measure_integrable rho (partial_function_total u) ->(forall x,~W x ->u x=0) ->
  exists a,is_measure_integral rho (partial_density_product (partial_function_total u) d) a /\
    is_measure_integral alpha (parameterized_integral beta
      (fun y=>partial_function_zero_extension (0:extended_real_line R) [set x|F x=y]
        (partial_function_total u))) a.
Proof.
move=>hDensity hMeas hPos [C [hC hBound]] hNonnegative [a hI] hOff.
have hPost (phi:extended_real_line R->extended_real_line R) x j:
    partial_function_graph (partial_function_postcompose (partial_function_total u) phi) x j <->
    partial_function_graph (partial_function_total (fun x=>phi (u x))) x j.
  split.
  - move=>[v [hv <-]]; by rewrite -(hv:u x=v).
  - move=>hj; exists (u x); by split.
have [P [N [hp [hneg [hP hN]]]]]:=measurable_function_parts_integrals hr hI.1.
have [z hz]:=integrable_function_part_difference_defined hr hI hp hneg hP hN.
have hpT:=measure_integral_graph_equivalent (hPost (@extended_positive_part R)) hp.
have hnT:=measure_integral_graph_equivalent (hPost (@extended_negative_part R)) hneg.
have hPOff x:~W x ->extended_positive_part (u x)=0.
  move=>hx; by rewrite (hOff x hx) /extended_positive_part maxxx.
have hNOff x:~W x ->extended_negative_part (u x)=0.
  move=>hx; by rewrite (hOff x hx) /extended_negative_part oppe0 /extended_positive_part maxxx.
have [P' [hpNu hpAlpha]]:=hNonnegative (fun x=>extended_positive_part (u x)) hpT.1
  (fun x=>extended_positive_part_nonnegative (u x)) hPOff.
have [N' [hnNu hnAlpha]]:=hNonnegative (fun x=>extended_negative_part (u x)) hnT.1
  (fun x=>extended_negative_part_nonnegative (u x)) hNOff.
have hP':0<=P':=nonnegative_total_integral_value_ge0 hn
  (fun x=>extended_positive_part_nonnegative (u x)) hpNu.
have hN':0<=N':=nonnegative_total_integral_value_ge0 hn
  (fun x=>extended_negative_part_nonnegative (u x)) hnNu.
have hPBound:=almost_bounded_density_integral_comparison hr hDensity hMeas hPos hC hBound
  (fun x=>extended_positive_part_nonnegative (u x)) hpT hpNu.
have hNBound:=almost_bounded_density_integral_comparison hr hDensity hMeas hPos hC hBound
  (fun x=>extended_negative_part_nonnegative (u x)) hnT hnNu.
have hFinite (b : \bar R):0<=b ->b< +oo ->C%:E*b< +oo.
  move=>hb0 hbFin.
  have hbNum:b \is a fin_num by rewrite(ge0_fin_numE hb0) hbFin.
  by rewrite -(fineK hbNum) -EFinM ltry.
have hOne:(P'< +oo)||(N'< +oo).
  have /orP[hPF|hNF]:=(nonnegative_difference_defined hP hN).1 (ex_intro _ z hz).
  - apply/orP; left; exact:(le_lt_trans hPBound (hFinite P hP hPF)).
  - apply/orP; right; exact:(le_lt_trans hNBound (hFinite N hN hNF)).
have [b hDifference]:=(nonnegative_difference_defined hP' hN').2 hOne.
have hpPart:is_measure_integral nu (partial_extended_function_positive_part (partial_function_total u)) P'.
  exact:(measure_integral_graph_equivalent (fun x j=>iff_sym (hPost (@extended_positive_part R) x j)) hpNu).
have hnPart:is_measure_integral nu (partial_extended_function_negative_part (partial_function_total u)) N'.
  exact:(measure_integral_graph_equivalent (fun x j=>iff_sym (hPost (@extended_negative_part R) x j)) hnNu).
have hSigned:=measure_integral_from_parts hn hpPart hnPart hDifference.
exists b; split.
- exact:((@measure_density_integral_iff R X rho nu hr d (partial_function_total u)
    hDensity hMeas hPos hI.1 b).1 hSigned).
- exact:(parameterized_subset_total_integral_from_parts ha hb hpAlpha hnAlpha hDifference).
Qed.
