(** Federer (1969), 2.10.46, p. 204: the Gross product identity for
    arbitrary factors, including infinite second measure. Take a Borel hull
    H of the product. Restrict first-factor Lebesgue measure to a
    finite-volume ball that still gives the arbitrary first set positive
    outer measure. The positive section-volume superlevel set of H is Borel,
    contains the second factor, and satisfies the proved Gross slicing
    bound. Thus infinite second mass forces infinite product mass, without
    assuming semifiniteness or a positive measurable subset of either
    original factor. This expands the printed reference to 2.10.8, p. 175.
    Source context and the two supporting steps: GrossBorelSectionLower.v
    and FiniteBorelSectionVolume.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates MetricProductRectangles
  EuclideanLebesgueDimensions EuclideanLebesgueHaar EuclideanLebesgueBoxes
  ProjectionMeasure MeasureUP MeasureBasic MeasureRestriction MeasureIndexedCover
  NonnegativeSum NonnegativeSumSupport TopologicalBorel BorelRegularMeasureUP ContinuousBorelPreimages
  ExtendedRealOrderTopology GrossBorelSectionLower FiniteBorelSectionVolume GrossArbitraryProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gross_arbitrary_product_infinite_second]:
    infinite-second-mass case of the Gross identity in
    2.10.46, p. 204. The first set has positive
    outer Lebesgue measure; neither set is required measurable,
    Borel, or covered by countably many finite-measure sets. *)
Theorem gross_arbitrary_product_infinite_second (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> 0<euclidean_lebesgue_measure m U -> @gross_measure R n k V=+oo ->
  @gross_measure R (m+n) (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)=+oo.
Proof.
move=> hkn hpos hVinf.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
have hm := euclidean_lebesgue_is_measure R m.
have [hWo hWc hWT] := @euclidean_ball_cover R m.
pose A j := U `&` @euclidean_open_ball_sequence R m j.
have hex : exists j, 0<euclidean_lebesgue_measure m (A j).
  apply: contrapT=> hn; exfalso.
  have hz j : euclidean_lebesgue_measure m (A j)=0.
    apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt.
    apply/negP=> hj; apply: hn; by exists j.
  have hcover : U `<=` \bigcup_j A j.
    move=> x hx; have [j hj] := hWT x; exists j=> //; by split.
  have hh := @measure_indexed_cover R X [the choiceType of (nat : Type)]
    (@euclidean_lebesgue_measure R m) hm U setT A (countableP setT) hcover.
  rewrite (nonnegative_sum_zero (fun j _=>hz j)) in hh.
  by have hbad := lt_le_trans hpos hh; rewrite ltxx in hbad.
have [j hj] := hex.
pose alpha := measure_restrict (@euclidean_lebesgue_measure R m) (@euclidean_open_ball_sequence R m j).
have ha : is_measure alpha := measure_restrict_is_measure hm _.
have hat : alpha setT< +oo.
  rewrite /alpha /measure_restrict setIT.
  have [K hK hWK] := hWc j.
  exact: le_lt_trans (measure_mono hm hWK) (euclidean_compact_finite hK).
have hau : 0<alpha U by rewrite /alpha /measure_restrict setIC.
have hab A0 : borel_set A0 -> measure_measurable alpha A0.
  move=> hA0; apply: (@measure_restrict_measurable R X (@euclidean_lebesgue_measure R m) _ A0).
  exact: euclidean_borel_measurable hA0.
have [q [hq0 hqu]] := @extended_rationals_order_dense R 0 (alpha U) hau.
pose c : R := ratr q.
have hc : (0<c)%R by move: hq0; rewrite lte_fin.
pose rect := metric_product_rectangle
  (fun z=>(@euclidean_block_split R m n z).1)
  (fun z=>(@euclidean_block_split R m n z).2).
have hdim : (m+k<=m+n)%N by rewrite leq_add2l.
have ht := @gross_measure_is_measure R (m+n) (m+k) hdim.
have hr := @gross_measure_borel_regular R (m+n) (m+k) hdim.
have [H [hSH [hH heH]]] := borel_regular_cover hr (rect U V).
pose J := (@euclidean_block_join R m n) @^-1` H.
have hJ : borel_set J := @continuous_borel_preimage (X*Y)%type _ (@euclidean_block_join R m n)
  (@euclidean_block_join_continuous R m n) H hH.
pose B := [set y : Y | c%:E<=alpha [set x | H (@euclidean_block_join R m n (x,y))]].
have [E hE] := euclidean_countable_open_base R m.
have [F hF] := euclidean_countable_open_base R n.
have hB : borel_set B := @finite_borel_horizontal_section_level R X Y alpha ha E F J c hE hF hat hab hJ.
have hVB : V `<=` B.
  move=> y hy; apply: le_trans (ltW hqu) _.
  apply: (measure_mono ha)=> x hx; apply: hSH.
  change (U ((@euclidean_block_split R m n (@euclidean_block_join R m n (x,y))).1) /\
    V ((@euclidean_block_split R m n (@euclidean_block_join R m n (x,y))).2)).
  by rewrite euclidean_block_joinK.
have hsec y : B y -> c%:E<=euclidean_lebesgue_measure m [set x | H (@euclidean_block_join R m n (x,y))].
  move=> hy; apply: le_trans hy _; apply: (measure_mono hm)=> x [_ hx]; exact hx.
have hbound := @gross_borel_horizontal_sections_lower_bound R m n k H B c hkn hH hB hc hsec.
have hBinf : @gross_measure R n k B=+oo.
  apply/eqP; rewrite eq_le leey andTb -hVinf.
  exact (@measure_mono R Y (@gross_measure R n k) (@gross_measure_is_measure R n k hkn) V B hVB).
rewrite hBinf muleC gt0_mulye ?lte_fin // in hbound.
rewrite heH; by apply/eqP; rewrite eq_le leey hbound.
Qed.

(** Source for [gross_product_identity]: the full Gross
    product equality of 2.10.46, p. 204, for arbitrary
    factors on the ordinary defined-product domain of 2.1.1,
    p. 51. All natural dimensions and infinite masses are
    included. Null second factors and zero-dimensional first
    factors use the independently proved endpoint conventions. *)
Theorem gross_product_identity (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> (@gross_measure R n k V< +oo \/ 0<euclidean_lebesgue_measure m U) ->
  @gross_measure R (m+n) (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)=
    euclidean_lebesgue_measure m U*@gross_measure R n k V.
Proof.
move=> hkn hdom; have [hf|hi] := ltP (@gross_measure R n k V) +oo.
  exact: gross_product_finite_second.
have hInf : @gross_measure R n k V=+oo by apply/eqP; rewrite eq_le leey hi.
have hp : 0<euclidean_lebesgue_measure m U.
  case: hdom=> // hf; by rewrite hInf ltxx in hf.
rewrite (@gross_arbitrary_product_infinite_second R m n k U V hkn hp hInf).
by rewrite hInf muleC gt0_mulye.
Qed.
