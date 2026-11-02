(** Federer (1969), 2.10.46, p. 204: the Gross product equality for
    arbitrary factors with finite first volume and finite second measure.
    Enclose both factors in equal-measure Borel supersets by 2.2.3, p. 61.
    The proved equality of measures on the enclosing finite rectangle then
    applies to the original, possibly nonmeasurable, product. The Cartesian
    outer-rectangle identity is proved from its own covering definition.
    Source context and finite-rectangle argument:
    GrossFiniteRectangleMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates MetricProductRectangles
  EuclideanLebesgueDimensions ProjectionMeasure MeasureUP MeasureBasic MeasureRestriction MeasurePushforward
  BorelRegularMeasureUP BorelRegularRestriction ProductMeasure RegularProductRectangleValue GrossFiniteRectangleMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gross_product_finite_outer_factors]: Gross
    product identity in 2.10.46, p. 204, for
    arbitrary finite-outer-measure factors in positive first
    dimension. No Borel or measurable-set hypothesis is imposed. *)
Theorem gross_product_finite_outer_factors (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> euclidean_lebesgue_measure m.+1 U< +oo -> @gross_measure R n k V< +oo ->
  @gross_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)=
    euclidean_lebesgue_measure m.+1 U*@gross_measure R n k V.
Proof.
move=> hkn hUf hVf.
have hm := euclidean_lebesgue_is_measure R m.+1.
have hr := euclidean_lebesgue_borel_regular R m.+1.
have hn := @gross_measure_is_measure R n k hkn.
have hs := @gross_measure_borel_regular R n k hkn.
have [S [hUS [hS heS]]] := borel_regular_cover hr U.
have [W [hVW [hW heW]]] := borel_regular_cover hs V.
have hSf : euclidean_lebesgue_measure m.+1 S< +oo by rewrite -heS.
have hWf : @gross_measure R n k W< +oo by rewrite -heW.
have hbox := @gross_finite_rectangle_product_measure R m n k hkn S W hS hW hSf hWf.
have hSU : S `&` U=U.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hUS.
have hWV : W `&` V=V.
  apply/seteqP; split=> [y [_ hy]|y hy] //; split=> //; exact: hVW.
have he := congr1 (fun mu=>mu (U `*` V)) hbox.
have hset : (metric_product_rectangle (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) S W) `&`
    ((@euclidean_block_split R m.+1 n) @^-1` (U `*` V))=
    metric_product_rectangle (fun z=>(@euclidean_block_split R m.+1 n z).1)
      (fun z=>(@euclidean_block_split R m.+1 n z).2) U V.
  apply/seteqP; split=> [z [_ hz]|z [hu hv]] //; split=> //; split.
  - exact: hUS hu.
  - exact: hVW hv.
rewrite /measure_pushforward /measure_restrict hset in he.
have hra := borel_regular_restrict_borel hm hr hS.
have hrb := borel_regular_restrict_borel hn hs hW.
have haf := measure_restrict_is_measure hm S.
have hbf := measure_restrict_is_measure hn W.
have hvf : measure_restrict (@gross_measure R n k) W V< +oo.
  by rewrite /measure_restrict hWV.
have hprod := @regular_product_arbitrary_rectangle_finite_second R _ _ _ _ haf hbf
  (borel_regular_is_regular haf hra) (borel_regular_is_regular hbf hrb) U V hvf.
have hpa : haf=measure_restrict_is_measure (euclidean_lebesgue_is_measure R m.+1) S := Prop_irrelevance _ _.
have hpb : hbf=measure_restrict_is_measure (@gross_measure_is_measure R n k hkn) W := Prop_irrelevance _ _.
rewrite hpa hpb in hprod.
rewrite hprod /measure_restrict hSU hWV in he; exact he.
Qed.
