(** Federer (1969), 2.10.46, p. 204: supporting identification on a finite
    Borel rectangle. The Gross product identity on Borel rectangles follows
    from 2.10.8. Borel rectangle covers give domination by the Cartesian
    product; equal finite total mass then gives equality on Borel sets and,
    by regular hulls, on arbitrary subsets. This makes the regularisation
    step explicit without adding measurability to the final arbitrary-factor
    statement. Source context: GrossBorelProductLower.v and
    BorelProductMeasureBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates MetricProductRectangles
  EuclideanRectangleBorel EuclideanLebesgueDimensions EuclideanLebesgueHaar
  ProjectionMeasure GrossBorelProduct MeasureUP MeasureBasic MeasureSplit MeasureRestriction MeasurePushforward
  MeasureCoordinateTransport BorelRegularMeasureUP BorelRegularRestriction TopologicalBorel BorelFamilyBasic
  ProductMeasure ProductRectangleValue ProductBorelRegularity BorelProductMeasureBound FiniteBorelMeasureAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gross_finite_rectangle_product_measure]: supporting
    equality of restricted measures for 2.10.46, p. 204.
    The containing rectangle is Borel with finite factor measures;
    the resulting equality applies to every subset of the product
    space, not only to Borel subsets. *)
Theorem gross_finite_rectangle_product_measure (R : realType) m n k (hkn : (k<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (W : set (inner_metric_space (@euclidean_inner_productP R n))) :
  borel_set S -> borel_set W -> euclidean_lebesgue_measure m.+1 S< +oo -> @gross_measure R n k W< +oo ->
  measure_pushforward (@euclidean_block_split R m.+1 n)
    (measure_restrict (@gross_measure R (m.+1+n) (m.+1+k))
      (metric_product_rectangle (fun z=>(@euclidean_block_split R m.+1 n z).1)
        (fun z=>(@euclidean_block_split R m.+1 n z).2) S W))=
  product_measure (measure_restrict_is_measure (euclidean_lebesgue_is_measure R m.+1) S)
    (measure_restrict_is_measure (@gross_measure_is_measure R n k hkn) W).
Proof.
move=> hS hW hSf hWf.
pose P := [the topologicalType of inner_metric_space (@euclidean_inner_productP R (m.+1+n))].
pose X := [the topologicalType of inner_metric_space (@euclidean_inner_productP R m.+1)].
pose Y := [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)].
pose rect := metric_product_rectangle (fun z=>(@euclidean_block_split R m.+1 n z).1)
  (fun z=>(@euclidean_block_split R m.+1 n z).2).
pose alpha := measure_restrict (@euclidean_lebesgue_measure R m.+1) S.
pose beta := measure_restrict (@gross_measure R n k) W.
have ha := measure_restrict_is_measure (euclidean_lebesgue_is_measure R m.+1) S.
have hb := measure_restrict_is_measure (@gross_measure_is_measure R n k hkn) W.
have hra : is_borel_regular_measure alpha := borel_regular_restrict_borel
  (euclidean_lebesgue_is_measure R m.+1) (euclidean_lebesgue_borel_regular R m.+1) hS.
have hrb : is_borel_regular_measure beta := borel_regular_restrict_borel
  (@gross_measure_is_measure R n k hkn) (@gross_measure_borel_regular R n k hkn) hW.
pose mu := measure_pushforward (@euclidean_block_split R m.+1 n)
  (measure_restrict (@gross_measure R (m.+1+n) (m.+1+k)) (rect S W)).
pose nu := product_measure ha hb.
have hdim : (m.+1+k<=m.+1+n)%N by rewrite leq_add2l.
have ht := @gross_measure_is_measure R (m.+1+n) (m.+1+k) hdim.
have htr := @gross_measure_borel_regular R (m.+1+n) (m.+1+k) hdim.
have hrest := measure_restrict_is_measure ht (rect S W).
have hm : is_measure mu.
  exact: measure_pushforward_is_measure hrest.
have hn : is_measure nu := product_measure_is_measure ha hb.
have hr : is_borel_regular_measure mu.
  apply: (@homeomorphic_pushforward_borel_regular R P (Topological.clone (X*Y)%type _)
    _ hrest (@euclidean_block_split R m.+1 n) (@euclidean_block_join R m.+1 n)
    (@euclidean_block_splitK R m.+1 n) (@euclidean_block_joinK R m.+1 n)
    (@euclidean_block_split_continuous R m.+1 n) (@euclidean_block_join_continuous R m.+1 n)).
  exact (@borel_regular_restrict_borel R P _ ht htr (rect S W)
    (@euclidean_rectangle_borel R m.+1 n S W hS hW)).
have hs : is_borel_regular_measure nu.
  have [C hC] := euclidean_countable_open_base R m.+1.
  have [D hD] := euclidean_countable_open_base R n.
  exact: (@product_measure_borel_regular R X Y alpha beta ha hb C D hC hD hra hrb).
have hrect A B : borel_set A -> borel_set B -> mu (A `*` B)=alpha A*beta B.
  move=> hA hB.
  have he : (rect S W) `&` ((@euclidean_block_split R m.+1 n) @^-1` (A `*` B))=
      rect (S `&` A) (W `&` B).
    apply/seteqP; split=> x [[h1 h2] [h3 h4]]; by split; split.
  rewrite /mu /measure_pushforward /measure_restrict he.
  have hSA := @borel_family_binary_intersection X setT _ (borel_sets_family X) S A hS hA.
  have hWB := @borel_family_binary_intersection Y setT _ (borel_sets_family Y) W B hW hB.
  have hWBf : @gross_measure R n k (W `&` B)< +oo.
    apply: le_lt_trans _ hWf; apply: (measure_mono (@gross_measure_is_measure R n k hkn))=> x [hx _]; exact hx.
  exact (@gross_borel_product_finite_second R m n k (S `&` A) (W `&` B) hkn hSA hWB hWBf).
have hdom : forall A, mu A<=nu A.
  apply: (@measure_bounded_by_borel_product_rectangles R X Y alpha beta ha hb mu hra hrb hm)=> A B hA hB.
  by rewrite hrect.
have htotal : mu setT=nu setT.
  have he : @setT (X*Y)=(@setT X `*` @setT Y).
    by apply/seteqP; split=> z _ //; split.
  rewrite he (hrect _ _ (open_borel_set openT) (open_borel_set openT)).
  exact: esym (product_measure_rectangle_value ha hb (measure_measurable_whole ha) (measure_measurable_whole hb)).
have hfinite : nu setT< +oo.
  rewrite -htotal /mu /measure_pushforward /measure_restrict preimage_setT setIT.
  rewrite (@gross_borel_product_finite_second R m n k S W hkn hS hW hWf).
  have hsf : euclidean_lebesgue_measure m.+1 S \is a fin_num
    by rewrite (ge0_fin_numE (measure_nonnegative (euclidean_lebesgue_is_measure R m.+1) S)).
  have hwf : @gross_measure R n k W \is a fin_num
    by rewrite (ge0_fin_numE (measure_nonnegative (@gross_measure_is_measure R n k hkn) W)).
  by rewrite -(fineK hsf) -(fineK hwf) -EFinM ltry.
have he := @finite_dominated_borel_regular_measures_agree R (Topological.clone (X*Y)%type _)
  mu nu hm hn hr hs hdom htotal hfinite.
have hpa : ha=measure_restrict_is_measure (euclidean_lebesgue_is_measure R m.+1) S := Prop_irrelevance _ _.
have hpb : hb=measure_restrict_is_measure (@gross_measure_is_measure R n k hkn) W := Prop_irrelevance _ _.
rewrite /mu /nu hpa hpb in he; exact he.
Qed.
