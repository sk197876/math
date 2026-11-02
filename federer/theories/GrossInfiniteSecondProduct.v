(** Federer (1969), 2.10.46, p. 204: the infinite second-mass case for a
    Lebesgue-measurable first factor and a Borel second factor. Positive
    first volume supplies a finite positive Borel subset by countable
    Euclidean exhaustion and the finite Borel sandwich of 2.2.3, p. 61. The
    already proved finite-first-volume Borel formula then forces infinite
    product measure. Source context and the Borel partition argument:
    GrossBorelProductLower.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates MetricProductRectangles
  EuclideanLebesgueDimensions EuclideanLebesgueHaar EuclideanLebesgueBoxes
  ProjectionMeasure MeasureUP MeasureBasic MeasureFiniteClosure MeasureIndexedCover
  NonnegativeSum NonnegativeSumSupport TopologicalBorel BorelRegularMeasureUP BorelRegularSandwich
  GrossFiniteBorelProduct GrossArbitraryProduct ProjectionProductEmptyBlock.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gross_measurable_first_infinite_borel_second]:
    infinite-second-mass consequence of the product equality
    in 2.10.46, p. 204. The first set may
    be non-Borel and unbounded, but is Lebesgue measurable
    with positive volume. The second set is Borel. *)
Theorem gross_measurable_first_infinite_borel_second (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> measure_measurable (@euclidean_lebesgue_measure R m.+1) U -> borel_set V ->
  0<euclidean_lebesgue_measure m.+1 U -> @gross_measure R n k V=+oo ->
  @gross_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)=+oo.
Proof.
move=> hkn hU hV hpos hVinf.
pose X := [the choiceType of inner_metric_space (@euclidean_inner_productP R m.+1)].
have hm := euclidean_lebesgue_is_measure R m.+1.
have hr := euclidean_lebesgue_borel_regular R m.+1.
have [hWo hWc hWT] := @euclidean_ball_cover R m.+1.
pose A j := U `&` @euclidean_open_ball_sequence R m.+1 j.
have hAm j : measure_measurable (@euclidean_lebesgue_measure R m.+1) (A j).
  apply: (@measure_measurable_intersection R X _ hm) hU _.
  exact: euclidean_borel_measurable (open_borel_set (hWo j)).
have hAf j : euclidean_lebesgue_measure m.+1 (A j)< +oo.
  have [C hC hWC] := hWc j.
  apply: le_lt_trans _ (euclidean_compact_finite hC).
  apply: (measure_mono hm)=> x [_ hx]; exact: hWC.
have hex : exists j, 0<euclidean_lebesgue_measure m.+1 (A j).
  apply: contrapT=> hn; exfalso.
  have hz j : euclidean_lebesgue_measure m.+1 (A j)=0.
    apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt.
    apply/negP=> hj; apply: hn; by exists j.
  have hcover : U `<=` \bigcup_j A j.
    move=> x hx; have [j hj] := hWT x; exists j=> //; by split.
  have hh := @measure_indexed_cover R X [the choiceType of (nat : Type)]
    (@euclidean_lebesgue_measure R m.+1) hm U setT A (countableP setT) hcover.
  rewrite (nonnegative_sum_zero (fun j _=>hz j)) in hh.
  by have hbad := lt_le_trans hpos hh; rewrite ltxx in hbad.
have [j hj] := hex.
have [D [B [hD [hB [hDA [hAB hz]]]]]] := borel_regular_finite_sandwich hm hr (hAm j) (hAf j).
have hDB : D `<=` B := subset_trans hDA hAB.
have hi : B `&` D=D.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hDB.
have hval := borel_regular_borel_measurable hm hr hD B.
rewrite hi hz adde0 in hval.
have he : euclidean_lebesgue_measure m.+1 D=euclidean_lebesgue_measure m.+1 (A j).
  apply: le_anti; apply/andP; split.
    exact (@measure_mono R X (@euclidean_lebesgue_measure R m.+1) hm D (A j) hDA).
  have hh := measure_mono hm hAB.
  by rewrite hval in hh.
have hDf : euclidean_lebesgue_measure m.+1 D< +oo by rewrite he.
have hDp : 0<euclidean_lebesgue_measure m.+1 D by rewrite he.
have hfinite : euclidean_lebesgue_measure m.+1 D \is a fin_num
  by rewrite (ge0_fin_numE (measure_nonnegative hm D)).
pose d := fine (euclidean_lebesgue_measure m.+1 D).
have hdval : euclidean_lebesgue_measure m.+1 D=d%:E := esym (fineK hfinite).
have hd : (0<d)%R by move: hDp; rewrite hdval lte_fin.
have hprod := @gross_finite_borel_product R m n k D V d hkn hD hV hdval (or_introl hd).
rewrite hVinf muleC gt0_mulye ?lte_fin // in hprod.
apply/eqP; rewrite eq_le leey /= -hprod.
have hdim : (m.+1+k<=m.+1+n)%N by rewrite leq_add2l.
apply: (measure_mono (@gross_measure_is_measure R (m.+1+n) (m.+1+k) hdim))=> x [hx hy].
split=> //; exact: (hDA _ hx).1.
Qed.

(** Source for [gross_measurable_borel_product]: product
    identity of 2.10.46, p. 204, for Lebesgue-measurable
    first factors and Borel second factors. Neither mass is
    required finite. The disjunction records the ordinary
    product domain of 2.1.1, p. 51; the zero-dimensional
    first factor uses the proved unit-mass convention. *)
Theorem gross_measurable_borel_product (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> measure_measurable (@euclidean_lebesgue_measure R m) U -> borel_set V ->
  (@gross_measure R n k V< +oo \/ 0<euclidean_lebesgue_measure m U) ->
  @gross_measure R (m+n) (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)=
    euclidean_lebesgue_measure m U*@gross_measure R n k V.
Proof.
case: m U=> [|m] U hkn hU hV hdom.
  exact: gross_product_empty_first_block.
have [hf|hi] := ltP (@gross_measure R n k V) +oo.
  exact: gross_product_finite_second.
have hInf : @gross_measure R n k V=+oo by apply/eqP; rewrite eq_le leey hi.
have hp : 0<euclidean_lebesgue_measure m.+1 U.
  case: hdom=> // hf; by rewrite hInf ltxx in hf.
rewrite (@gross_measurable_first_infinite_borel_second R m n k U V hkn hU hV hp hInf).
by rewrite hInf muleC gt0_mulye.
Qed.
