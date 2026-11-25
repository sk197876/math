(** Federer (1969), 3.2.11, p. 249: the jointly
    measurable translated fibre mass, cut off on the auxiliary
    ball. Its horizontal integrals are computed by translation
    invariance, then Fubini supplies the other order. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes CoareaJointTranslationMeasurable CoareaTranslationIntegral
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension MeasurableZeroExtension MeasurableFunctionUP
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence MeasureConullZeroIntegral MeasureNonnegativeIntegral
  MeasureExtendedCharacteristicIntegral CharacteristicFunctionUP CharacteristicFunctionSealed
  PartialExtendedOrderLoci CountablyMeasurableUP CountablyMeasurableFunctions
  CountablyMeasurableProduct CountablyMeasurableNullModification ProductMeasure ProductSecondCylinder ProductFunctionFubini
  PartialProductSections PartialFunctionPrecomposition ParameterizedIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_translated_cutoff]: the integrand
    theta(y-epsilon*z) for z in the auxiliary ball, zero
    otherwise, in Federer 3.2.11, p. 249.
    This prescribed formula uses the existing sealed zero extension. *)
Definition coarea_translated_cutoff (R:realType) n
    (theta:inner_metric_space (@euclidean_inner_productP R n)->extended_real_line R)
    (e:R) (B:set (R_n R n)):=
  partial_function_zero_extension (0:extended_real_line R) (setT `*` B)
    (partial_function_total (fun yz=>theta (yz.1-e*:yz.2)%R)).

(** Source for [coarea_translated_cutoff_measurable]: the
    application of 3.1.3(3) and measurable restriction before
    Fubini in Federer 3.2.11, p. 249. *)
Lemma coarea_translated_cutoff_measurable (R:realType) n theta e B:
  measure_measurable (@euclidean_lebesgue_measure R n) B ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R n) (partial_function_total theta) ->
  is_measure_measurable_function
    (product_measure (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_is_measure R n))
    (@coarea_translated_cutoff R n theta e B).
Proof.
move=>hB ht; apply:(measurable_zero_extension
  (product_measure_is_measure (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_is_measure R n))).
- exact (product_second_cylinder_measurable (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_is_measure R n) hB).
- exact:coarea_joint_scaled_translation_measurable ht.
Qed.

(** Source for [coarea_translated_cutoff_horizontal_integral]:
    the translated inner integral in Federer 3.2.11,
    p. 249 equals the original integral on the ball
    and zero off it. The cutoff is described by its laws. *)
Lemma coarea_translated_cutoff_horizontal_integral (R:realType) n theta e B
    (chi:R_n R n->R) a:
  is_characteristic_function B chi ->(forall y,0<=theta y) ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (partial_function_total theta) a ->
  forall z,is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_product_horizontal_section (@coarea_translated_cutoff R n theta e B) z)
    (a*(chi z)%:E).
Proof.
move=>hchi hp hi z; case:(pselect (B z))=>hz.
- rewrite (characteristic_on_set hchi hz) mule1.
  have ht:=coarea_scaled_translation_integral e z hp hi.
  apply:(measure_integral_graph_equivalent _ ht)=>y t.
  change (theta (y-e*:z)%R=t <->
    partial_function_graph (coarea_translated_cutoff theta e B) (y,z) t).
  rewrite /coarea_translated_cutoff (@partial_function_zero_extension_on _ _ 0 _ _ (y,z) t (conj Logic.I hz)).
  by [].
- rewrite (characteristic_off_set hchi hz) mule0.
  apply:(measure_almost_zero_integral (euclidean_lebesgue_is_measure R n)).
  apply:(measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R n)
    _ (measure_almost_everywhere_true (euclidean_lebesgue_is_measure R n)))=>y _.
  change (partial_function_graph (coarea_translated_cutoff theta e B) (y,z) 0).
  rewrite /coarea_translated_cutoff partial_function_zero_extension_off //.
  by move=>[_ h]; exact:hz h.
Qed.

(** Source for [coarea_translated_cutoff_fubini]: the two
    integral orders in Federer 3.2.11, p. 249.
    The product and vertical iterated integrals equal the
    original theta integral times the auxiliary set's mass;
    all infinite nonnegative values are retained. *)
Theorem coarea_translated_cutoff_fubini (R:realType) n theta e B a:
  measure_measurable (@euclidean_lebesgue_measure R n) B ->
  (forall y,0<=theta y) ->0<=a ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (partial_function_total theta) a ->
  is_measure_integral
    (product_measure (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_is_measure R n))
    (coarea_translated_cutoff theta e B) (a*euclidean_lebesgue_measure n B) /\
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (parameterized_integral (@euclidean_lebesgue_measure R n)
      (partial_product_vertical_section (coarea_translated_cutoff theta e B)))
    (a*euclidean_lebesgue_measure n B).
Proof.
move=>hB hp ha hi.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose hm:=euclidean_lebesgue_is_measure R n.
pose mu:=@euclidean_lebesgue_measure R n.
pose nu:=product_measure hm hm.
pose hn:=product_measure_is_measure hm hm.
pose F:=coarea_translated_cutoff theta e B.
have hFm:=coarea_translated_cutoff_measurable e hB hi.1.
have hFp:measure_almost_everywhere nu (partial_extended_nonnegative_locus F).
  apply:(measure_almost_everywhere_mono hn _ (measure_almost_everywhere_true hn))=> -[y z] _.
  case:(pselect (B z))=>hz.
  - exists (theta (y-e*:z)%R); split; last exact:hp.
    rewrite /F /coarea_translated_cutoff
      (@partial_function_zero_extension_on _ _ 0 _ _ (y,z) (theta (y-e*:z)%R) (conj Logic.I hz)).
    by [].
  - exists 0; split; last exact:lexx.
    rewrite /F /coarea_translated_cutoff partial_function_zero_extension_off //.
    by move=>[_ h]; exact:hz h.
have [b hb]:=nonnegative_measurable_function_integrable hn hFm hFp.
have hWhole:=product_whole_countably_measurable hm hm
  (euclidean_lebesgue_countably_measurable R n) (euclidean_lebesgue_countably_measurable R n).
have hCount:=countably_measurable_function_on_countable_source hn
  (@extended_real_zero_closed R) hWhole hFm.
have [hVert hHoriz]:=@product_function_fubini R [the choiceType of X] [the choiceType of X] mu mu hm hm F b hb hCount.
pose chi:=@CharacteristicFunction.value R X B.
have hchi:=@CharacteristicFunction.laws R X B.
have hInt z:=coarea_translated_cutoff_horizontal_integral e hchi hp hi z.
have hChar:=measure_nonnegative_extended_characteristic_integral hm hchi hB ha.
have hHoriz':is_measure_integral mu
    (parameterized_integral mu (partial_product_horizontal_section F)) (a*mu B).
  apply:(measure_integral_graph_equivalent _ hChar)=>z t.
  change (a*(chi z)%:E=t <->
    partial_function_graph (parameterized_integral mu (partial_product_horizontal_section F)) z t).
  rewrite parameterized_integral_specification; split=>h.
  - rewrite -h; exact:hInt.
  - exact:measure_integral_unique (hInt z) h.
have hEq:=measure_integral_unique hHoriz hHoriz'.
by rewrite hEq in hb hVert; split.
Qed.
