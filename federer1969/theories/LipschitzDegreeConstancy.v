(** Federer (1969), 4.1.26, pp. 383–384:
    the original signed degree is Lebesgue
    almost constant on each component of
    R^m minus f(Bdry A). The proof follows
    the book: exact image-boundary support, old
    top-current constancy, then almost uniqueness of
    the original locally summable scalar density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm InnerMetric HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorGrading CurrentSpaces CurrentDensityUP CurrentDensityAction CurrentDensitySealed
  EuclideanCharacteristicCurrent EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  MetricDiameter LipschitzUP LipschitzBasic CurrentFlatLipschitzPushforwardSealed
  CurrentBoundedCharacteristicFlat LipschitzDegreeSealed LipschitzDegreeCharacteristicImage
  LipschitzDegreeBoundaryImage TopCurrentAllDegreeConstancy TopDensityOpenAlmostConstancy
  PartialDensityAlmostConstancy PartialFunctionUP PartialFunctionExtensionUP PartialFunctionExtensionSealed
  NormOpenComponents MeasureUP MeasureAlmostUP MeasureAlmostBasic
  CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_degree_image_boundary_carried]:
    the last displayed support inclusion in
    the proof of 4.1.26, p. 384,
    with the vacuous ambient-dimension-zero boundary
    case recorded explicitly. *)
Theorem lipschitz_degree_image_boundary_carried (R:realType)
    (h2:(1+1:R)!=0) m:
  forall (f:R_n R m->R_n R m)
    (hLip:@is_metric_lipschitz R
      (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R m)) setT f)
    (A:set (R_n R m))
    (hA:measure_measurable (@euclidean_lebesgue_measure R m) A)
    (hBound:@metric_set_bounded R
      (inner_metric_space (@euclidean_inner_productP R m)) A),
  let Full:=fun _:R_n R m=>True in
  let hFull:=fun x (_:True)=>norm_full_domain_interior
    (inner_norm (@euclidean_inner_productP R m)) x in
  let hLocal:=@metric_lipschitz_is_local R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m))) setT f hLip in
  @top_current_boundary_carried R h2 m
    (@CurrentFlatLipschitzPushforward.value R h2 m m m Full Full hFull hFull
      f (fun _ _=>Logic.I) hLocal (@euclidean_characteristic_current R h2 m A hA)
      (@current_bounded_characteristic_flat R h2 m A hA hBound))
    (f @` lipschitz_degree_source_boundary A).
Proof.
case:m=>[|p] f hLip A hA hBound Full hFull hLocal;first exact:Logic.I.
exact:(@lipschitz_degree_image_boundary_support R h2 p f hLip A hA hBound).
Qed.

(** Source for [lipschitz_degree_component_almost_constant]:
    the final assertion on p. 383 of
    4.1.26: degree(f|A) is Lebesgue almost
    constant on every component outside f(Bdry A).
    The original hypotheses are exactly global
    Lipschitz continuity and bounded Lebesgue measurability
    of A. No normality or degree bound occurs. *)
Theorem lipschitz_degree_component_almost_constant (R:realType)
    (h2:(1+1:R)!=0) m (f:R_n R m->R_n R m)
    (hLip:@is_metric_lipschitz R
      (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R m)) setT f)
    (A:set (R_n R m))
    (hA:measure_measurable (@euclidean_lebesgue_measure R m) A)
    (hBound:@metric_set_bounded R
      (inner_metric_space (@euclidean_inner_productP R m)) A) a:
  ~(f @` lipschitz_degree_source_boundary A) a->
  exists c:R,measure_almost_everywhere_on (@euclidean_lebesgue_measure R m)
    (@connected_component (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m)))
      (~`(f @` lipschitz_degree_source_boundary A)) a)
    [set y|partial_function_graph (@LipschitzDegree.value R m f A) y c].
Proof.
move=>ha.
pose X:=R_n R m.
pose N:=inner_norm (@euclidean_inner_productP R m).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose NT:=real_norm_metric_space hN.
pose Full:=fun _:X=>True.
pose hFull:=fun (x:X) (_:True)=>norm_full_domain_interior N x.
pose hLocal:=@metric_lipschitz_is_local R NT NT setT f hLip.
pose Q:=@CurrentFlatLipschitzPushforward.value R h2 m m m Full Full hFull hFull
  f (fun _ _=>Logic.I) hLocal (@euclidean_characteristic_current R h2 m A hA)
  (@current_bounded_characteristic_flat R h2 m A hA hBound).
pose B:=f @` lipschitz_degree_source_boundary A.
have hB:@closed NT B:=compact_closed (@metric_hausdorff R NT)
  (@lipschitz_degree_boundary_image_compact R m f hLip A hBound).
have[c hConstancy]:=@top_current_all_degree_component_constancy R h2 m Q B hB
  (@lipschitz_degree_image_boundary_carried R h2 m f hLip A hA hBound) a ha.
pose W:=@connected_component NT (~` B) a.
have hW:@open NT W.
  apply:(@norm_open_components_open R X N hN (~` B) a);by rewrite openC.
pose d:=@LipschitzDegree.value R m f A.
pose r:=@PartialFunctionExtension.value X R d 0.
have hR:is_partial_function_total_extension d r:=@PartialFunctionExtension.laws X R d 0.
have[hField _]:=@lipschitz_degree_current_density R h2 m f hLip A hA hBound r hR.
have hAction:=@lipschitz_degree_current_action R h2 m f hLip A hA hBound r hR.
have hAlmost:=@top_density_open_almost_constant R h2 m r hField Q hAction W hW c hConstancy.
exists c;exact:(@partial_density_almost_constant_from_extension R X
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m)
  d r W c hR (@lipschitz_degree_conull_domain R h2 m f hLip A hA hBound) hAlmost).
Qed.
