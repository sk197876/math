(** Federer (1969), 2.10.46, p. 204: extend the Borel product equality to
    every Lebesgue-measurable first factor when the second factor is Borel
    with finite Gross measure. The Borel sandwich and finite exhaustion use
    2.2.3, pp. 61–62, and 2.1.3, pp. 54–55. The first-factor slice measure
    need not itself be Borel regular. Arbitrary nonmeasurable factors remain
    a separate obligation. Source context: BorelRectangleFirstSlice.v and
    GrossBorelProductLower.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates MetricProductRectangles
  EuclideanLebesgueDimensions EuclideanLebesgueHaar EuclideanLebesgueBoxes
  ProjectionMeasure MeasureUP MeasureBasic TopologicalBorel TopologicalProductMaps
  GrossBorelProduct GrossProductNullFactor MetricRectangleFirstSlice BorelRectangleFirstSlice
  BorelFiniteIncreasingCover BorelScaledCompletionAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gross_measurable_product_finite_second]: product
    identity of 2.10.46, p. 204, for all
    Lebesgue-measurable first factors in positive dimension and
    Borel second factors with finite Gross measure. Infinite
    first volume and a null second factor are included. *)
Theorem gross_measurable_product_finite_second (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> measure_measurable (@euclidean_lebesgue_measure R m.+1) U ->
  borel_set V -> (@gross_measure R n k V< +oo)%E ->
  @gross_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)=
    (euclidean_lebesgue_measure m.+1 U*@gross_measure R n k V)%E.
Proof.
move=> hkn hU hV hfin.
have [hz|hnz] := eqVneq (@gross_measure R n k V) 0%E.
  by rewrite (@gross_product_null_second_factor R m.+1 n k V hkn hz U) hz mule0.
have hvnon := measure_nonnegative (@gross_measure_is_measure R n k hkn) V.
have hvfin : @gross_measure R n k V \is a fin_num by rewrite (ge0_fin_numE hvnon).
pose v := fine (@gross_measure R n k V).
have hve : @gross_measure R n k V=v%:E := esym (fineK hvfin).
have hv : 0<v.
  have hh : (0<@gross_measure R n k V)%E by rewrite lt_def hnz hvnon.
  by move: hh; rewrite hve lte_fin.
pose P := [the metricType R of inner_metric_space (@euclidean_inner_productP R (m.+1+n))].
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose first := fun z=>(@euclidean_block_split R m.+1 n z).1.
pose second := fun z=>(@euclidean_block_split R m.+1 n z).2.
pose rho := fun A : set X=>@gross_measure R (m.+1+n) (m.+1+k)
  (metric_product_rectangle first second A V).
have hdim : (m.+1+k<=m.+1+n)%N by rewrite leq_add2l.
have ht := @gross_measure_is_measure R (m.+1+n) (m.+1+k) hdim.
have hrt := @gross_measure_borel_regular R (m.+1+n) (m.+1+k) hdim.
have hrho := @metric_rectangle_first_slice_is_measure R P X Y first second V _ ht.
have hfirst : continuous first.
  move=> x; exact: continuous_comp (@euclidean_block_split_continuous R m.+1 n x)
    (@first_projection_continuous X Y (@euclidean_block_split R m.+1 n x)).
have hb B : borel_set B -> measure_measurable rho B.
  exact: (@borel_rectangle_first_slice_measurable R P X Y first second V _ ht hrt hfirst B).
have he B : borel_set B -> rho B=(v%:E*euclidean_lebesgue_measure m.+1 B)%E.
  move=> hB; rewrite /rho (@gross_borel_product_finite_second R m n k B V hkn hB hV hfin).
  by rewrite hve muleC.
have hm := euclidean_lebesgue_is_measure R m.+1.
have hr := euclidean_lebesgue_borel_regular R m.+1.
have [hWo hWc hWT] := @euclidean_ball_cover R m.+1.
have hWf j : (euclidean_lebesgue_measure m.+1 (@euclidean_open_ball_sequence R m.+1 j)< +oo)%E.
  have [C hC hWC] := hWc j.
  exact: le_lt_trans (measure_mono hm hWC) (euclidean_compact_finite hC).
have [E [hE [hEf [hEm hcov]]]] := @borel_finite_increasing_cover R X
  (@euclidean_lebesgue_measure R m.+1) (@euclidean_open_ball_sequence R m.+1) hm hr hWf.
have hwhole x : exists j, E j x.
  have [j hj] := hWT x.
  have hx : (\bigcup_j @euclidean_open_ball_sequence R m.+1 j) x by exists j.
  have [l _ hl] := hcov x hx; by exists l.
have hh := (@borel_scaled_agreement_completed_measure R X rho
  (@euclidean_lebesgue_measure R m.+1) hrho hm hr v E hv hb he hE hEf hEm hwhole U hU).2.
rewrite hve muleC; exact hh.
Qed.
