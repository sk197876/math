(** Federer (1969), 3.4.4, p. 318: the
    original Cantor correspondence has the required flat extension. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals topology lra.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP RealMetricBackground
  EuclideanOneCoordinate EuclideanOneNormDifferential PowerCantorPairUP PowerCantorPair
  BinaryCantorCodingExistence BinaryCantorMatchingUP BinaryCantorHomeomorphism
  BinaryCantorHolder BinaryCantorScalePowers MetricSubsetBackground HomeomorphismUP
  SymmetricForms ContinuousMultilinearSealed NormRegularity NormHigherSymmetricFormUP
  FlatWhitneyHolderExtension RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCantor.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 1)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 1)).
Local Notation hN:=(inner_norm_real_norm (@euclidean_inner_productP R 1)).
Local Notation hS:=(@scalar_absolute_value_norm R).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i (R_n R 1) R^o N (fun t:R^o=>`|t|) hN hS).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i (R_n R 1) R^o N (fun t:R^o=>`|t|) hN hS).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i (R_n R 1) R^o N (fun t:R^o=>`|t|) hN hS).

(** Source for [binary_cantor_flat_extension_exists]: the
    map g with all printed value and flatness properties,
    3.4.4, p. 318. The existing canonical
    isometry identifies the source line with R^1.
    Original equal-cost trees supply the correspondence; its
    proved Holder bound verifies the full Whitney hypothesis.
    The exact original image is retained. *)
Theorem binary_cantor_flat_extension_exists (alpha beta:R) k
    (A B:set (real_line_metric R)) (f h:R->R):
  0<alpha ->alpha<1 ->0<beta ->beta<1 ->k%:R<alpha/beta ->
  is_power_cantor_pair 1 alpha (fun _:nat=>2%N) A f ->
  is_power_cantor_pair 1 beta (fun _:nat=>2%N) B h ->
  exists g:E->R^o,norm_class hN hS (fun _=>True) g k /\
    (fun t:real_line_metric R=>g (euclidean_one_embed t)) @` A=B /\
    forall a,A a ->forall i,(1<=i<=k)%N ->
      is_norm_higher_differential_form N ev ZN (fun _=>True) g i
        (euclidean_one_embed a) 0.
Proof.
move=>hAlpha hAlphaUpper hBeta hBetaUpper hOrder hPairA hPairB.
have hCompactA:compact A:=(power_cantor_pair_properties ltr01 hAlpha hAlphaUpper hPairA).1.
have hClosedA:closed A:=compact_closed (@metric_hausdorff R [the metricType R of real_line_metric R]) hCompactA.
have [JA [HA [hJA [hTreeA [hLimitA hFunctionA]]]]]:=hPairA.
have [JB [HB [hJB [hTreeB [hLimitB hFunctionB]]]]]:=hPairB.
have [I [a hCodeA]]:=@binary_original_coding_exists R 1 alpha JA HA ltr01 hAlpha hAlphaUpper hJA hTreeA.
have [J [b hCodeB]]:=@binary_original_coding_exists R 1 beta JB HB ltr01 hBeta hBetaUpper hJB hTreeB.
have [phi [psi [hPhi [hPsi hHomeo]]]]:=@binary_cantor_homeomorphism_exists R alpha beta
  JA HA I a JB HB J b A B hAlpha hAlphaUpper hBeta hBetaUpper hCodeA hCodeB hLimitA hLimitB.
pose C:=real_power (1-2*real_power 2 (-alpha^-1)) (-(alpha/beta)).
have [hRho hGap]:=binary_cantor_scale_bounds hAlpha hAlphaUpper.
have hC:0<C:=@real_power_strictly_positive R (1-2*real_power 2 (-alpha^-1)) (-(alpha/beta)) hGap.
pose S:set E:=fun x=>A (euclidean_one_project x).
pose phi1:E->R^o:=fun x=>phi (euclidean_one_project x).
have hClosedS:closed S.
  apply:(@preimage_closed [the topologicalType of E] [the topologicalType of real_line_metric R]
    (@euclidean_one_project R) A).
  - move=>x _;exact:euclidean_one_project_continuous.
  - exact:hClosedA.
have hHolder x y:S x ->S y ->`|phi1 x-phi1 y|<=C*real_power (N (x-y)) (alpha/beta).
  move=>hx hy.
  have hBound:=@binary_cantor_printed_holder_bound R alpha beta JA HA I a JB HB J b A B phi
    hAlpha hAlphaUpper hBeta hCodeA hCodeB hLimitA hPhi
    (euclidean_one_project x) (euclidean_one_project y) hx hy.
  by rewrite /C /phi1 euclidean_one_norm_coordinate /euclidean_one_project !ffunE.
have [g [hG [hValues hFlat]]]:=@flat_whitney_holder_extension_exists R 1 R^o
  (fun t:R^o=>`|t|) hS S phi1 k C (alpha/beta) hClosedS hC hOrder hHolder.
exists g;split=>//;split.
- apply/seteqP;split=>y.
  + move=>[x hx <-].
    have hxS:S (euclidean_one_embed x) by rewrite /S euclidean_one_embedK.
    rewrite (hValues _ hxS) /phi1 euclidean_one_embedK.
    exact:(@binary_cantor_correspondence_maps R A B I J phi hPhi x hx).
  + move=>hy.
    pose yB:metric_subset B:=Sub y (mem_set hy).
    pose xA:=binary_cantor_subset_correspondence hPsi yB.
    have hInverse:=congr1 val (homeomorphism_right_inverse hHomeo yB).
    exists (val xA);first exact:set_valP xA.
    have hxS:S (euclidean_one_embed (val xA)) by rewrite /S euclidean_one_embedK;exact:set_valP xA.
    rewrite (hValues _ hxS) /phi1 euclidean_one_embedK.
    exact:hInverse.
- move=>a0 ha0 i hi;apply:hFlat=>//.
  by rewrite /S euclidean_one_embedK.
Qed.
End FlatCantor.
