(** Federer (1969), 3.2.11, p. 249: combine
    full target rank and critical target rank on a Borel
    subset of the actual differentiability locus. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions EuclideanLipschitzClassZero TopologicalBorel BorelFamilyBasic
  CoareaRankLoci CoordinateInverseCoverUP CoareaJacobianMeasure CriticalCoareaJacobianZero
  FullRankBorelCoarea BorelCriticalCoarea CoareaCriticalFibreNull
  NormDifferentialUP LipschitzUP HausdorffMeasure MappingMultiplicity MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureNullModification MeasureIntegralUP MeasureIntegralAlmostEquality
  PartialFunctionUP PartialFunctionBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [differentiable_borel_coarea]: the two
    rank cases in the proof of Federer 3.2.11,
    p. 249 give coarea on every Borel set
    of actual differentiability points, with no finite-mass premise. *)
Theorem differentiable_borel_coarea (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  (n<m)%N ->is_metric_lipschitz setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] A ->
  (forall x,A x ->norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f x) ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f A y)
        :extended_real_line R))) (euclidean_coarea_measure f A).
Proof.
move=>hnm hf hA hDiff.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
pose nu:=euclidean_coarea_measure f.
pose hn:=euclidean_coarea_measure_is_measure hf.
pose beta:=@hausdorff_measure R X (m-n).
pose hb:=@hausdorff_measure_is_measure R X (m-n).
pose C:=A `&`surjective_differential_locus f.
pose S:=A `&`critical_target_differential_locus f.
have hCont:=euclidean_lipschitz_norm_class_zero hf.
have hCB:borel_set C:=borel_family_binary_intersection (borel_sets_family X) hA
  (surjective_target_differential_locus_borel hCont).
have hSB:borel_set S:=borel_family_binary_intersection (borel_sets_family X) hA
  (critical_target_differential_locus_borel hCont).
have hC:A `<=`fun x=>~S x ->C x.
  move=>x hx hnS; split=> //.
  have [hRank|hCritical]:=(ordinary_target_rank_split f x).1 (hDiff x hx); first exact hRank.
  by exfalso; apply:hnS; split.
have hCA:C `<=`A by move=>x [hx _].
have hZero:nu S=0.
  apply:critical_coarea_jacobian_measure_zero=>x [_ hx]; exact hx.
have hCriticalIntegral:=borel_critical_coarea hnm hf hSB (fun x (hx:S x)=>hx.2).
fold nu in hCriticalIntegral.
rewrite hZero in hCriticalIntegral.
have hFibreZero:=coarea_zero_fibre_integral_almost_null hCriticalIntegral.
have hValue:nu C=nu A.
  apply:(measure_null_modification_value hn hZero)=>x hx.
  split; first exact:hCA.
  move=>ha; exact (hC x ha hx).
have hFull:=full_rank_borel_coarea hnm hf hCB (fun x (hx:C x)=>hx.2).
fold nu; rewrite -hValue.
apply:(measure_integral_almost_equal hm hFull).
apply:(@measure_almost_everywhere_mono R _ mu hm _ _ _ hFibreZero)=>y hy.
have hEq:beta (mapping_fibre f C y)=beta (mapping_fibre f A y).
  apply:(measure_null_modification_value hb hy)=>x hx.
  split.
  - move=>[hc he]; split=> //; exact:hCA.
  - move=>[ha he]; split=> //; apply:(hC x ha)=>hs.
    exact (hx (conj hs he)).
exists (beta (mapping_fibre f C y)); split; first by [].
change (beta (mapping_fibre f A y)=beta (mapping_fibre f C y)).
exact:Logic.eq_sym hEq.
Qed.
