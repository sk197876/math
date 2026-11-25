(** Federer (1969), 2.10.46, p. 204: supporting arbitrary-factor product
    identity when the second factor is covered by countably many sets of
    finite Gross measure. This includes infinite second mass and
    nonmeasurable factors. The countable cover is an explicit intermediate
    hypothesis, not an assumption about all Gross-measurable sets. Borel
    regularity supplies an increasing finite Borel cover, and 2.1.3(4), p.
    55, applies to Gross measure restricted to the second factor. Source
    context and the finite-factor argument: GrossArbitraryProduct.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates MetricProductRectangles
  EuclideanLebesgueDimensions ProjectionMeasure MeasureUP MeasureBasic MeasureRestriction BorelRegularMeasureUP
  BorelFiniteIncreasingCover MeasureContinuityBelow ExtendedIncreasingLimitSupremum ExtendedRealOrderTopology
  ExtendedRealBoundsUP GrossArbitraryProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gross_infinite_sigma_finite_second_product]:
    supporting infinite-mass case of 2.10.46, p. 204.
    Both sets may be nonmeasurable. The second set has a
    countable finite-measure cover, and the first has positive
    outer Lebesgue measure. *)
Theorem gross_infinite_sigma_finite_second_product (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n)))
    (C : nat -> set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> (forall j, @gross_measure R n k (C j)< +oo) ->
  V `<=` \bigcup_j C j -> 0<euclidean_lebesgue_measure m U -> @gross_measure R n k V=+oo ->
  @gross_measure R (m+n) (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)=+oo.
Proof.
move=> hkn hC hcov hp hInf.
have hm := @gross_measure_is_measure R n k hkn.
have hr := @gross_measure_borel_regular R n k hkn.
have [E [hE [hEf [hEm hCE]]]] := @borel_finite_increasing_cover R _ _ C hm hr hC.
have hVE : V `<=` \bigcup_j E j := subset_trans hcov hCE.
have he : V `&` (\bigcup_j E j)=V.
  apply/seteqP; split=> [x [hx _]|x hx] //; split=> //; exact: hVE.
have hEr j : measure_measurable (measure_restrict (@gross_measure R n k) V) (E j).
  apply: (@measure_restrict_measurable R _ (@gross_measure R n k) V (E j)).
  exact (@borel_regular_borel_measurable R _ _ hm hr (E j) (hE j)).
have hlim := @measure_continuity_below R _ _ (measure_restrict_is_measure hm V) E hEr hEm.
rewrite /measure_restrict he in hlim.
have hsup := extended_increasing_limit_supremum hlim.
have [q [hq0 hqU]] := @extended_rationals_order_dense R 0 (euclidean_lebesgue_measure m U) hp.
have hq : (0<(ratr q : R))%R by move: hq0; rewrite lte_fin.
pose rect := metric_product_rectangle
  (fun z=>(@euclidean_block_split R m n z).1)
  (fun z=>(@euclidean_block_split R m n z).2).
have hdim : (m+k<=m+n)%N by rewrite leq_add2l.
have ht := @gross_measure_is_measure R (m+n) (m+k) hdim.
have hb : (ratr q : R)%:E*@gross_measure R n k V<=@gross_measure R (m+n) (m+k) (rect U V).
  rewrite -lee_pdivlMl //; apply: (extended_real_supremum_least hsup)=> z [j ->].
  rewrite lee_pdivlMl //.
  have hfin : @gross_measure R n k (V `&` E j)< +oo.
    apply: le_lt_trans _ (hEf j); apply: (measure_mono hm)=> x [_ hx]; exact hx.
  apply: le_trans (lee_wpmul2r (measure_nonnegative hm (V `&` E j)) (ltW hqU)) _.
  rewrite -(@gross_product_finite_second R m n k U (V `&` E j) hkn hfin).
  apply: (measure_mono ht)=> x [hx [hy _]]; by split.
rewrite hInf muleC gt0_mulye ?lte_fin // in hb.
by apply/eqP; rewrite eq_le leey hb.
Qed.

(** Source for [gross_sigma_finite_second_product]:
    intermediate form of the product identity in 2.10.46,
    p. 204, for arbitrary factors with a countable finite
    Gross-measure cover of the second factor. The domain
    excludes the undefined zero-times-infinity expression of
    2.1.1, p. 51, without assuming semifiniteness. *)
Theorem gross_sigma_finite_second_product (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n)))
    (C : nat -> set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> (forall j, @gross_measure R n k (C j)< +oo) ->
  V `<=` \bigcup_j C j ->
  (@gross_measure R n k V< +oo \/ 0<euclidean_lebesgue_measure m U) ->
  @gross_measure R (m+n) (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)=
    euclidean_lebesgue_measure m U*@gross_measure R n k V.
Proof.
move=> hkn hC hcov hdom.
have [hf|hi] := ltP (@gross_measure R n k V) +oo.
  exact: gross_product_finite_second.
have hInf : @gross_measure R n k V=+oo by apply/eqP; rewrite eq_le leey hi.
have hp : 0<euclidean_lebesgue_measure m U.
  case: hdom=> // hf; by rewrite hInf ltxx in hf.
rewrite (@gross_infinite_sigma_finite_second_product R m n k U V C hkn hC hcov hp hInf).
by rewrite hInf muleC gt0_mulye.
Qed.
