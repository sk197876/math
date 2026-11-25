(** Federer (1969), 3.3.19, p. 304:
    supporting exact perimeter of an actual simple
    closed parameter curve. Derive the length identity
    from 2.10.13, p. 177, retaining its two
    source endpoints and removing only their null image. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  CurveVariationUP CurveLengthMultiplicity MappingMultiplicity MappingMultiplicityLaws MappingPartitionMultiplicity
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralAlmostEquality MeasureExtendedCharacteristicIntegral
  CharacteristicFunctionUP CharacteristicFunctionSealed HausdorffMeasure HausdorffClosedCoverAgreement HausdorffCountableNull
  BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simple_closed_curve_image_length]:
    the actual length comparison used for the cyclic
    boundary points in 3.3.19, p. 304.
    A continuous curve injective on [a,b), with
    equal endpoint values, has variation equal to
    the actual H1 mass of its image. Infinite
    lengths are retained. No Jordan theorem is assumed. *)
Theorem simple_closed_curve_image_length (R:realType) (Y:metricType R)
    (g:R->Y) (a b:R):
  continuous (g:real_line_metric R->Y) ->a<b ->g a= g b ->
  {in (`[a,b[:set R) &,injective g} ->
  @hausdorff_measure R Y 1 (g @` (`[a,b]:set R))= curve_variation g a b.
Proof.
move=>hContinuous hab hEnds hInjective.
pose A:set (real_line_metric R):=`[a,b[.
pose B:set (real_line_metric R):=`[a,b].
pose E:= g @` B.
pose mu:= @hausdorff_measure R Y 1.
have hMu:= @hausdorff_measure_is_measure R Y 1.
have hA a':A a' ->B a'.
  rewrite /A /B /= !in_itv /= =>/andP[hLow hHigh];by rewrite hLow (ltW hHigh).
have hImage:g @` A= E.
  apply/seteqP;split=>y.
  - move=>[t ht hValue];exists t=>//;exact:hA.
  - move=>[t ht hValue].
    move:ht;rewrite /B /= in_itv /= =>/andP[htA htB].
    case:(ltP t b)=>htStrict.
    + exists t=>//;by rewrite /A /= in_itv /= htA htStrict.
    + have hTB:t= b by lra.
      exists a.
      * by rewrite /A /= in_itv /= lexx hab.
      * by rewrite hEnds -hTB.
have hCompact:compact E:= continuous_compact (continuous_subspaceT hContinuous) (@segment_compact R a b).
have hBorel:borel_set E:= closed_borel_set (compact_closed (@metric_hausdorff R Y) hCompact).
pose chi:= @CharacteristicFunction.value R Y E.
have hChi:= @CharacteristicFunction.laws R Y E.
have hChar:is_characteristic_function (g @` A) chi by rewrite hImage.
have hSingle:= @injective_mapping_multiplicity_characteristic R [the choiceType of real_line_metric R]
  Y g A chi hInjective hChar.
have hFibre y:y!= g b ->mapping_fibre g A y= mapping_fibre g B y.
  move=>hy;apply:(@mapping_fibre_sandwich_equal [the choiceType of real_line_metric R] Y g A B B y hA (fun t ht=>ht)).
  move=>[t [htB htA] hValue].
  move:htB;rewrite /B /= in_itv /= =>/andP[htLow htHigh].
  have hTB:t= b.
    case:(ltP t b)=>hStrict;last by lra.
    exfalso;apply:htA;by rewrite /A /= in_itv /= htLow hStrict.
  by move:hy;rewrite -hTB hValue eqxx.
have hConull:measure_almost_everywhere mu [set y|y!= g b].
  have hComplement:~` [set y:Y|y!= g b]=[set g b].
    apply/seteqP;split=>y.
    + move=>hy;case:(eqVneq y (g b))=>[hEqual|hDifferent];first exact hEqual.
      exfalso;exact:hy hDifferent.
    + move=>->;change (~is_true (g b!=g b));by rewrite eqxx.
  rewrite /measure_almost_everywhere hComplement.
  exact:(@hausdorff_positive_degree_singleton_zero R Y 1 (g b) (erefl true)).
have hAgreement:measure_almost_equal mu
    (partial_function_total (fun y=>(@mapping_multiplicity R [the choiceType of real_line_metric R] Y g B y:extended_real_line R)))
    (partial_function_total (fun y=>((chi y)%:E:extended_real_line R))).
  apply:(@measure_almost_everywhere_mono R Y mu hMu _ _ _ hConull)=>y hy.
  exists ((chi y)%:E:extended_real_line R);split;last exact:erefl.
  change (@mapping_multiplicity R [the choiceType of real_line_metric R] Y g B y=(chi y)%:E).
  rewrite /mapping_multiplicity -(hFibre y hy).
  exact:hSingle.
have hLength:= @federer_2_10_13_length R Y g a b hContinuous hab.
have hCharacteristic:= @measure_total_characteristic_integral R Y mu hMu E chi hChi
  (@borel_regular_borel_measurable R Y mu hMu
    (@hausdorff_measure_borel_regular R Y 1) E hBorel).
apply:(measure_integral_unique hCharacteristic).
exact:(@measure_integral_almost_equal R Y mu hMu _ _ _ hLength hAgreement).
Qed.
