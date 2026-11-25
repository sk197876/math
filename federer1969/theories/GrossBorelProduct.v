(** Federer (1969), 2.10.46, p. 204: extend the Gross product identity from
    finite-volume Borel first factors to all Borel first factors when the
    second mass is finite. Use a finite Borel exhaustion of Euclidean space
    and the continuity-below theorem 2.1.3(4), p. 55. The upper estimate
    already holds without measurability assumptions. Source context and the
    partition step: GrossBorelProductLower.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates MetricProductRectangles
  EuclideanLebesgueDimensions EuclideanLebesgueHaar EuclideanLebesgueBoxes
  ProjectionMeasure MeasureUP MeasureBasic TopologicalBorel BorelFamilyBasic
  GrossFiniteBorelProduct GrossProductUpperBound GrossProductNullFactor
  BorelFiniteIncreasingCover MeasureContinuityBelow ExtendedIncreasingLimitSupremum ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gross_borel_product_finite_second]: Gross
    product identity of 2.10.46, p. 204, for
    Borel factors, positive first dimension, and finite second
    mass. Infinite first volume is included; the null second
    factor uses its independent nullity proof. *)
Theorem gross_borel_product_finite_second (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> borel_set U -> borel_set V -> (@gross_measure R n k V< +oo)%E ->
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
have hA j : borel_set (A j) := @borel_family_binary_intersection _ setT _ (borel_sets_family _) U (E j) hU (hE j).
have hAfin j : (euclidean_lebesgue_measure m.+1 (A j)< +oo)%E.
  apply: le_lt_trans _ (hEf j); apply: (measure_mono hm)=> x [_ hx]; exact hx.
have hAm j l : (j<=l)%N -> A j `<=` A l.
  move=> hjl x [hx hEx]; split=> //; exact (hEm j l hjl x hEx).
have hAU : (\bigcup_j A j)=U.
  apply/seteqP; split=> [x [j _ [hx _]]|x hx] //.
  have [j hj] := hWT x.
  have hxwhole : (\bigcup_j @euclidean_open_ball_sequence R m.+1 j) x by exists j.
  have [l _ hl] := hcov x hxwhole.
  exists l=> //; by split.
have hlim := @measure_continuity_below R _ _ hm A
  (fun j=>@euclidean_borel_measurable R m.+1 (A j) (hA j)) hAm.
rewrite hAU in hlim.
have hsup := extended_increasing_limit_supremum hlim.
have hupp := @gross_product_upper_finite_second R m n k U V hkn hfin.
apply/eqP; rewrite eq_le hupp /= hve muleC -lee_pdivlMl //.
apply: (extended_real_supremum_least hsup)=> z [j ->].
rewrite lee_pdivlMl // muleC -hve.
have ha0 := measure_nonnegative hm (A j).
have haf : euclidean_lebesgue_measure m.+1 (A j) \is a fin_num by rewrite (ge0_fin_numE ha0).
have hae : euclidean_lebesgue_measure m.+1 (A j)=(fine (euclidean_lebesgue_measure m.+1 (A j)))%:E := esym (fineK haf).
have he := @gross_finite_borel_product R m n k (A j) V
  (fine (euclidean_lebesgue_measure m.+1 (A j))) hkn (hA j) hV hae (or_intror hfin).
rewrite hae -he.
apply: (measure_mono htarget)=> x [[hx _] hy]; by split.
Qed.
