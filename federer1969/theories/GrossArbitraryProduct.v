(** Federer (1969), 2.10.46, p. 204: the Gross
    product formula for arbitrary factors with finite second
    measure. Exhaust the first space by finite Borel sets,
    applying continuity below to Lebesgue measure restricted to
    the possibly nonmeasurable first factor. Continuity below
    on arbitrary increasing sets is not assumed. The finite
    rectangle argument is in GrossFiniteOuterProduct.v; source
    editions and background are recorded there. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates MetricProductRectangles
  EuclideanLebesgueDimensions EuclideanLebesgueHaar EuclideanLebesgueBoxes
  ProjectionMeasure ProjectionProductEmptyBlock MeasureUP MeasureBasic MeasureRestriction TopologicalBorel BorelFamilyBasic
  GrossFiniteOuterProduct GrossProductUpperBound GrossProductNullFactor
  BorelFiniteIncreasingCover MeasureContinuityBelow ExtendedIncreasingLimitSupremum ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gross_arbitrary_product_finite_second]: Gross
    product identity of 2.10.46, p. 204, for
    arbitrary factors in positive first dimension and finite
    second mass. Infinite first outer volume and null second
    factors are included without measurability assumptions. *)
Theorem gross_arbitrary_product_finite_second (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> (@gross_measure R n k V< +oo)%E ->
  @gross_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)=
    (euclidean_lebesgue_measure m.+1 U*@gross_measure R n k V)%E.
Proof.
move=> hkn hfin.
have [hz|hnz] := eqVneq (@gross_measure R n k V) 0%E.
  by rewrite (@gross_product_null_second_factor R m.+1 n k V hkn hz U) hz mule0.
have hvnon := measure_nonnegative (@gross_measure_is_measure R n k hkn) V.
have hvfin : @gross_measure R n k V \is a fin_num by rewrite (ge0_fin_numE hvnon).
pose v := fine (@gross_measure R n k V).
have hve : @gross_measure R n k V=v%:E := esym (fineK hvfin).
have hv : 0<v.
  have hh : (0<@gross_measure R n k V)%E by rewrite lt_def hnz hvnon.
  by move: hh; rewrite hve lte_fin.
have hdim : (m.+1+k<=m.+1+n)%N by rewrite leq_add2l.
have htarget := @gross_measure_is_measure R (m.+1+n) (m.+1+k) hdim.
have hm := euclidean_lebesgue_is_measure R m.+1.
have hr := euclidean_lebesgue_borel_regular R m.+1.
have [hWo hWc hWT] := @euclidean_ball_cover R m.+1.
have hWf j : (euclidean_lebesgue_measure m.+1 (@euclidean_open_ball_sequence R m.+1 j)< +oo)%E.
  have [C hC hWC] := hWc j.
  exact: le_lt_trans (measure_mono hm hWC) (euclidean_compact_finite hC).
have [E [hE [hEf [hEm hcov]]]] := @borel_finite_increasing_cover R
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R m.+1)]
  (@euclidean_lebesgue_measure R m.+1) (@euclidean_open_ball_sequence R m.+1) hm hr hWf.
pose A j := U `&` E j.
have hAfin j : (euclidean_lebesgue_measure m.+1 (A j)< +oo)%E.
  apply: le_lt_trans _ (hEf j); apply: (measure_mono hm)=> x [_ hx]; exact hx.
have hEU : (\bigcup_j E j)=setT.
  apply/seteqP; split=> // x _.
  have [j hj] := hWT x.
  have hxwhole : (\bigcup_j @euclidean_open_ball_sequence R m.+1 j) x by exists j.
  exact: hcov x hxwhole.
have hEmu j : measure_measurable (measure_restrict (@euclidean_lebesgue_measure R m.+1) U) (E j).
  apply: measure_restrict_measurable; exact: euclidean_borel_measurable (hE j).
have hlim := @measure_continuity_below R _ _ (measure_restrict_is_measure hm U) E hEmu hEm.
rewrite hEU /measure_restrict setIT in hlim.
have hsup := extended_increasing_limit_supremum hlim.
have hupp := @gross_product_upper_finite_second R m n k U V hkn hfin.
apply/eqP; rewrite eq_le hupp /= hve muleC -lee_pdivlMl //.
apply: (extended_real_supremum_least hsup)=> z [j ->].
rewrite lee_pdivlMl // muleC -hve.
have he := @gross_product_finite_outer_factors R m n k (A j) V hkn (hAfin j) hfin.
rewrite -he.
apply: (measure_mono htarget)=> x [[hx _] hy]; by split.
Qed.

(** Source for [gross_product_finite_second]: product equality
    of 2.10.46, p. 204, for arbitrary sets
    with finite second Gross mass, with the explicitly documented
    zero-dimensional first-factor extension. No measurability or
    finiteness of the first factor is assumed. *)
Theorem gross_product_finite_second (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> (@gross_measure R n k V< +oo)%E ->
  @gross_measure R (m+n) (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)=
    (euclidean_lebesgue_measure m U*@gross_measure R n k V)%E.
Proof.
case: m U=> [|m] U hkn hfin.
- exact: gross_product_empty_first_block.
- exact: gross_arbitrary_product_finite_second.
Qed.
