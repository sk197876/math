(** Federer (1969), 3.4.8(13), p. 336:
    intersect the finitely many original coordinate representatives.
    Their common germ is preserved; all coordinate multiplicity
    bounds apply to the intersection. The proved projection
    estimate gives finite mass and uniform diameter growth. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExteriorIndices InitialIndices
  SetGermUP SetGermFiniteIntersection CoordinateProjection MappingMultiplicity CurveFiniteMultiplicity
  MetricClosedBalls CoordinateMultiplicityBallGrowth HausdorffBallDiameterGrowth UniformHausdorffGrowthUP
  RectifiableSetUP CountablyMeasureRectifiableOperations HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP TopologicalBorel
  EuclideanLebesgueDimensions EuclideanClosedBallGrowth CompactMetricBounded CompactSetDistanceProfile
  MetricDiameterUP MetricDiameter MetricBoundedClosureLaws CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [common_coordinate_growth_representative]: the final
    intersection and Hausdorff growth argument in 3.4.8(13),
    p. 336. Finite mass is proved from
    the coordinate counts, not imposed on the original models. *)
Theorem common_coordinate_growth_representative (R:realType) n m (hMN:(m<=n)%N)
    (H:set (R_n R n)) (F:Lambda n m->set (R_n R n)) (c:Lambda n m->R):
  (0<m)%N ->
  (forall lambda,@compact (inner_metric_space (@euclidean_inner_productP R n)) (F lambda)) ->
  (forall lambda,@set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 (F lambda)=
    @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 H) ->
  (forall lambda,@is_countably_measure_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n))
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) m (F lambda)) ->
  (forall lambda,0<=c lambda) ->
  (forall lambda,measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    [set y|(@mapping_multiplicity R (inner_metric_space (@euclidean_inner_productP R n))
      (R_n R m) (@coordinate_projection R n m lambda) (F lambda) y<=(c lambda)%:E)%E]) ->
  exists (S:set (R_n R n)) (b:R),
    @compact (inner_metric_space (@euclidean_inner_productP R n)) S /\
    @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 S=
      @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 H /\
    @is_measure_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n))
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) m S /\
    @is_uniform_hausdorff_growth R (inner_metric_space (@euclidean_inner_productP R n)) m S b.
Proof.
move=>hPositive hCompact hGerm hRect hC hCaps.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Top:=Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _.
pose mu:=@hausdorff_measure R X m.
pose lambda0:=@Lambda_initial m n hMN.
pose S:set X:=\bigcap_lambda F lambda.
have hSF lambda:S `<=` F lambda by move=>x hx;exact:hx lambda Logic.I.
have hClosed:closed S.
  apply:closed_bigI=>lambda _.
  exact:compact_closed (@metric_hausdorff R X) (hCompact lambda).
have hCompactS:compact S.
  have hEqual:S=F lambda0 `&` S by apply/seteqP;split=>[x hx|x [hx hSx]];[split;[exact:hSF lambda0 x hx|exact:hx]|exact:hSx].
  rewrite hEqual;exact:compact_closedI (hCompact lambda0) hClosed.
have hSGerm:@set_germ Top 0 S=@set_germ Top 0 H.
  exact:(@set_germ_finite_common_intersection Top 0 (Finite.clone (Lambda n m) _) lambda0 F H hGerm).
have hCount:=@countably_measure_rectifiable_subset R X mu m (F lambda0) S (hSF lambda0) (hRect lambda0).
have hMu:=@hausdorff_measure_is_measure R X m.
have hMeas:measure_measurable mu S.
  apply:(borel_regular_borel_measurable hMu (@hausdorff_measure_borel_regular R X m)).
  exact:closed_borel_set hClosed.
have hBoundS:metric_set_bounded S.
  case:(pselect (S !=set0))=>hNonempty.
  - pose K:compact_metric_set X:=exist _ S (mem_set (conj hCompactS hNonempty)).
    exact:(@compact_metric_diameter_finite R X K).
  - have hEmpty:S=set0 by apply/seteqP;split=>[x hx|x []];exfalso;apply:hNonempty;by exists x.
    rewrite hEmpty;exact:metric_bounded_empty.
have hCap lambda:measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    [set y|(@mapping_multiplicity R X (R_n R m) (@coordinate_projection R n m lambda) S y<=(c lambda)%:E)%E].
  apply:(measure_almost_everywhere_mono (@euclidean_lebesgue_is_measure R m) _ (hCaps lambda))=>y hy.
  apply:(le_trans _ hy).
  exact:(@mapping_multiplicity_subset_bound R X (R_n R m) (@coordinate_projection R n m lambda)
    S (F lambda) (hSF lambda) y).
pose b:=(\sum_lambda c lambda)*@euclidean_closed_unit_volume R m.
have hBNonnegative:0<=b.
  apply:mulr_ge0;last exact:ltW (@euclidean_closed_unit_volume_laws R m).2.
  exact:sumr_ge0 (fun lambda _=>hC lambda).
have hBalls x r:0<r ->(mu (S `&` metric_closed_ball x r)<=(b*r^+m)%:E)%E.
  exact:(@coordinate_multiplicity_hausdorff_ball_growth R n m hMN S c x r hC hCount hMeas hCap).
have hGrowth:@is_uniform_hausdorff_growth R X m S b.
  constructor;[exact:hBoundS|exact:hBNonnegative|].
  move=>T hTS.
  exact:(@hausdorff_ball_diameter_growth R X m S b hPositive hBNonnegative hBalls T hTS
    (metric_bounded_subset hTS hBoundS)).
have hFinite:(mu S< +oo)%E.
  have hMass:=@uniform_hausdorff_growth_bound R X m S b hGrowth S (fun x hx=>hx).
  have hDNonnegative:=metric_diameter_nonnegative (extended_metric_diameter_specification S).
  have hDFinite:extended_metric_diameter S \is a fin_num by rewrite (ge0_fin_numE hDNonnegative);exact:hBoundS.
  have hD:extended_metric_diameter S=(fine (extended_metric_diameter S))%:E:=esym (fineK hDFinite).
  apply:(le_lt_trans hMass).
  by rewrite hD -EFin_expe -EFinM ltry.
exists S,b;split;first exact:hCompactS.
split;first exact:hSGerm.
split;last exact:hGrowth.
by split.
Qed.
