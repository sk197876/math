(** Federer (1969), 3.2.32, pp. 269–270: the
    whole positive-fibre coarea corollary for the original partial
    map, with all temporary extensions eliminated from its statement. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  EuclideanPartialLipschitzExtension MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure
  RectifiableSetUP MappingMultiplicity MeasureApproximateDifferentialUP MeasureApproximateJacobian
  RectifiablePositiveFibreCoareaUP RectifiablePositiveFibreCoareaGlobal MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_2_32]: the complete corollary
    Federer 3.2.32, pp. 269–270. For an H^m-measurable
    finite (H^m,m)-rectifiable original domain and a Lipschitz map
    on exactly that domain, the approximate differential image has
    dimension at most mu almost everywhere above positive-mass
    complementary fibres, and the printed unweighted coarea
    identity holds there. All natural 0<=mu<=m, zero dimensions,
    zero Lipschitz bounds, infinite fibres and infinite integral
    values are retained. The proof expands the printed threshold
    limit with Borel target hulls, actual source restrictions,
    original-differential agreement and null-target Jacobian control. *)
Theorem federer_3_2_32 (R:realType) n v m mu
    (f:partial_function (R_n R n) (R_n R v)) L:
  (mu<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m (partial_function_domain f) ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) (partial_function_domain f) ->
  @is_partial_metric_lipschitz_bound R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) f L ->
  is_rectifiable_positive_fibre_coarea m mu f.
Proof.
move=>hDim hRect hW hLip.
pose W:=partial_function_domain f.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
have hH:=@hausdorff_measure_is_measure R X m.
have [F [hBound hGraph]]:=@euclidean_partial_lipschitz_global_extension R n v f L hLip.
have hF:=metric_lipschitz_of_bound hBound.
have hPreimage (A:set (R_n R v)):partial_function_preimage f A=W `&` F @^-1` A.
  apply/seteqP; split=>x.
  - move=>[y [hxy hy]].
    have hx:W x by exists y.
    rewrite hGraph in hxy; split=>//; change (A (F x)); by rewrite hxy.2.
  - move=>[hx hy]; exists (F x); split=>//; rewrite hGraph; by split.
have hFibre y:partial_function_preimage f [set y]=mapping_fibre F W y:=hPreimage [set y].
pose Y:set (R_n R v):=[set y|0<@hausdorff_measure R X (m-mu) (mapping_fibre F W y)].
have hY:positive_partial_fibre_locus m mu f=Y.
  apply:funext=>y.
  change (is_true (0<@hausdorff_measure R X (m-mu) (partial_function_preimage f [set y]))=
    is_true (0<@hausdorff_measure R X (m-mu) (mapping_fibre F W y))).
  by rewrite hFibre.
have hA:partial_function_preimage f (positive_partial_fibre_locus m mu f)=W `&` F @^-1` Y.
  by rewrite hY hPreimage.
have hResult:=@rectifiable_positive_fibre_coarea_global R m n mu v W F hDim hRect hW hF.
constructor.
- rewrite hA.
  apply:(measure_null_subset hH _ hResult.1)=>x [[hx hy] hNot].
  split; first by split.
  move=>[d [hd hImage]]; apply:hNot.
  split; first exact hx.
  exists d; split; last exact hImage.
  rewrite -hGraph in hd; exact hd.
- have [a [hSource hTarget]]:=hResult.2.
  exists a; split.
  + rewrite -hGraph in hSource.
    rewrite hA; exact hSource.
  + apply:(measure_integral_graph_equivalent _ hTarget)=>y z.
    change (@hausdorff_measure R X (m-mu) (mapping_fibre F W y)=z <->
      @hausdorff_measure R X (m-mu) (partial_function_preimage f [set y])=z).
    by rewrite hFibre.
Qed.
