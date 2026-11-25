(** Federer (1969), 3.2.11, p. 249: null
    changes of the source preserve complementary fibre mass
    almost everywhere, by 2.10.25 and 2.10.35. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanHausdorffLebesgue CoareaNullFibres NullFibresProperSource HausdorffMeasure MappingMultiplicity
  LipschitzUP MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureNullModification
  PartialFunctionUP PartialFunctionBasic MeasureIntegralUP MeasureIntegralAlmostEquality
  CoareaJacobianMeasure ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_null_source_fibres_zero]: the
    initial null-source case of Federer 3.2.11, p. 249,
    with arbitrary m>=n and the exact m-n fibre degree. *)
Lemma coarea_null_source_fibres_zero (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  (n<=m)%N ->is_metric_lipschitz setT f ->euclidean_lebesgue_measure m A=0 ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set y|@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m))
      (m-n) (mapping_fibre f A y)=0].
Proof.
move=>hnm [L [hL hBound]] hA.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
have hHaus:@hausdorff_measure R X ((m-n)+n) A=0.
  have hDegree:=congr1 (fun d:nat=>@hausdorff_measure R X d A) (subnK hnm).
  by rewrite hDegree (euclidean_hausdorff_spherical_lebesgue A).1.
have hNull:=@null_hausdorff_fibres_proper_source R X Y f L A (m-n) n
  (@coarea_euclidean_source_proper R m) hBound hHaus.
have hTarget:(@hausdorff_measure R Y n)=(@euclidean_lebesgue_measure R n).
  apply:funext=>B; exact (euclidean_hausdorff_spherical_lebesgue B).1.
by rewrite hTarget in hNull.
Qed.

(** Source for [coarea_null_source_fibre_mass_agreement]:
    the Borel-core and Rademacher reductions in Federer
    3.2.11, p. 249 preserve fibre masses almost
    everywhere, including infinite masses and nonmeasurable fibres. *)
Lemma coarea_null_source_fibre_mass_agreement (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) C A:
  (n<=m)%N ->is_metric_lipschitz setT f ->C `<=` A ->euclidean_lebesgue_measure m (A `\` C)=0 ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set y|@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m))
      (m-n) (mapping_fibre f C y)=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m))
      (m-n) (mapping_fibre f A y)].
Proof.
move=>hnm hf hCA hNull.
have hFibre:=coarea_null_source_fibres_zero hnm hf hNull.
apply:(@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R n) _ _ _ hFibre)=>y hy.
apply:(measure_null_modification_value (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R m)) (m-n)) hy)=>x hx.
split.
- move=>[hc he]; split=> //; exact:hCA.
- move=>[ha he]; split=> //; apply:contrapT=>hn; exact (hx (conj (conj ha hn) he)).
Qed.

(** Source for [coarea_null_source_integral_transfer]:
    integral transport in the initial reductions of Federer
    3.2.11, p. 249. The null source deficit
    also has zero Jacobian density measure. *)
Theorem coarea_null_source_integral_transfer (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) C A:
  (n<=m)%N ->is_metric_lipschitz setT f ->C `<=` A ->euclidean_lebesgue_measure m (A `\` C)=0 ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f C y)
        :extended_real_line R))) (euclidean_coarea_measure f C) ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f A y)
        :extended_real_line R))) (euclidean_coarea_measure f A).
Proof.
move=>hnm hf hCA hNull hI.
pose nu:=euclidean_coarea_measure f.
have hNuNull:nu (A `\` C)=0:=euclidean_coarea_measure_null f hNull.
have hValue:nu C=nu A.
  apply:(measure_null_modification_value (euclidean_coarea_measure_is_measure hf) hNuNull)=>x hx.
  split; first exact:hCA.
  move=>ha; apply:contrapT=>hn; exact (hx (conj ha hn)).
fold nu; rewrite -hValue.
apply:(measure_integral_almost_equal (euclidean_lebesgue_is_measure R n) hI).
apply:(@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R n) _ _ _
  (coarea_null_source_fibre_mass_agreement hnm hf hCA hNull))=>y hy.
exists (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f C y)).
split; first by [].
change (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f A y)=
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f C y)).
exact:Logic.eq_sym hy.
Qed.
