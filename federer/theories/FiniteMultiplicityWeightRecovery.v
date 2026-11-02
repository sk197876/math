(** Federer (1969), 3.2.5(2), p. 245: where
    multiplicity is finite and positive, recover the real
    weight from the measurable product g times multiplicity.
    The scalar division is an equivalent expansion of the
    printed characteristic-level formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  RealMetricBackground ExtendedRealOrderTopology ExtendedFiniteProjectionBorel RealReciprocalBorel
  PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasurableGraphEquivalence MeasurableTotalBasic MeasurableRealArithmetic
  LipschitzUP HausdorffMeasure MappingMultiplicity MappingMultiplicityLaws EuclideanAreaFormula AreaTransformIntegrands.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_multiplicity_measurable_weight_recovery]: the
    recovery argument for condition (2) in Federer 3.2.5,
    p. 245. Its representative agrees with g on f(A)
    outside the actual null infinite-multiplicity set; values
    there are used only inside the proof. *)
Theorem finite_multiplicity_measurable_weight_recovery (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A
    (g:R_n R n->real_line_metric R):
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  measure_almost_everywhere (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    [set y|@mapping_multiplicity R _ _ f A y< +oo] ->
  is_measure_measurable_function (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (area_transform_target_integrand f A g) ->
  exists G N,is_measure_measurable_function
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) (partial_function_total G) /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m N=0 /\
    forall y,(f @` A) y -> ~N y -> G y=g y.
Proof.
move=>hLip hA hFinite hTarget.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R Y m.
have hb:=@hausdorff_measure_is_measure R Y m.
pose M y:=@mapping_multiplicity R _ _ f A y.
have [a [hSource hCount]]:=euclidean_area_formula hLip hA.
pose F y:=(fine ((g y)%:E*M y):real_line_metric R).
pose V y:=(fine (M y):real_line_metric R).
pose G (y:Y):real_line_metric R:=(F y*(V y)^-1)%R.
have hF:=@measurable_total_borel_postcomposition R Y (extended_real_line R)
  [the topologicalType of real_line_metric R] beta hb
  (fun y=>((g y)%:E*M y:extended_real_line R)) (fun z=>(fine z:real_line_metric R))
  hTarget (@extended_finite_projection_borel R).
have hV:=@measurable_total_borel_postcomposition R Y (extended_real_line R)
  [the topologicalType of real_line_metric R] beta hb
  (fun y=>(M y:extended_real_line R)) (fun z=>(fine z:real_line_metric R))
  hCount.1 (@extended_finite_projection_borel R).
have hInv:=@measurable_total_borel_postcomposition R Y [the topologicalType of real_line_metric R]
  [the topologicalType of real_line_metric R] beta hb V (fun r=>(r^-1)%R) hV (@real_reciprocal_borel R).
have hProduct:=measurable_real_function_multiply hb hF hInv.
have hG:is_measure_measurable_function beta (partial_function_total G).
  apply:(@measurable_function_graph_equivalent R Y [the topologicalType of real_line_metric R]
    beta (partial_real_function_multiply (partial_function_total F)
      (partial_function_total (fun y=>((V y)^-1)%R))) (partial_function_total G) _ hProduct).
  move=>y z; split.
  - move=>[[r s] [[hr hs] he]]; change (F y=r) in hr; change (((V y)^-1)%R=s) in hs.
    change (G y=z); by rewrite /G hr hs.
  - move=>hz; change (G y=z) in hz; exists (F y,((V y)^-1)%R); by split; first split.
pose N:=(~` [set y|M y< +oo]).
exists G,N; split; first exact hG; split; first exact hFinite.
move=>y hImage hNot.
have hFin:M y< +oo by apply:contrapT=>hBad; exact (hNot hBad).
have hNonneg:0<=M y:=@mapping_multiplicity_nonnegative R _ _ f A y.
have hNum:M y \is a fin_num by rewrite (ge0_fin_numE hNonneg).
have hRep:M y=(fine (M y))%:E:=esym (fineK hNum).
have hNZ:M y<>0.
  move=>hZero; exact ((@mapping_multiplicity_zero_iff R _ _ f A y).1 hZero hImage).
have hV0:V y!=0%R.
  apply/negP=>/eqP hZero; apply:hNZ; by rewrite hRep -/(V y) hZero.
have hFValue:F y=(g y*V y)%R.
  by rewrite /F hRep -EFinM.
by rewrite /G hFValue -mulrA (mulfV hV0) mulr1.
Qed.
