(** Supporting the original product bound in Federer (1969), 3.2.45, p. 280.
    Reuse Borel regularisation and the Haar argument of 2.10.45, p. 203. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology EuclideanInnerProduct InnerMetric
  EuclideanCartesianMap EuclideanAdditiveGroup IntegralGeometricMeasure
  ConvexGeometricProductSlice ConvexGeometricProductCompactFinite
  MeasureUP MeasurePushforward TopologicalBorel BorelRegularMeasureUP
  BorelRegularisation BorelRegularisationBijection TranslationInvariantHaar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_geometric_product_slice_regularised_invariant]:
    supporting Haar hypothesis in the product proof of
    Federer 3.2.45, p. 280. The Borel regularisation
    retains the original slice values on Borel sets,
    compact finiteness and translation invariance. The
    second factor is arbitrary apart from its finite
    Q_1 mass. No regularity of the original slice
    measure on arbitrary first-factor sets is assumed. *)
Theorem convex_geometric_product_slice_regularised_invariant (R : realType) m n k (hKN : (k <= n)%N)
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (@convex_integral_geometric_measure R n k hKN 1 V < +oo)%E ->
  is_invariant_borel_measure (fun x y : inner_metric_space (@euclidean_inner_productP R m) => x+y)
    (borel_regularisation (fun U : set (inner_metric_space (@euclidean_inner_productP R m)) =>
      @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
        (euclidean_cartesian_set U V))).
Proof.
move=> hV.
pose gamma := fun U : set (inner_metric_space (@euclidean_inner_productP R m)) =>
  @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
    (euclidean_cartesian_set U V).
have hm := @convex_geometric_product_slice_is_measure R m n k hKN V.
have hb A (hA : borel_set A) : measure_measurable gamma A.
  exact (@convex_geometric_product_slice_borel_measurable R m n k hKN V A hA).
constructor.
- exact: borel_regularised_measure_is_measure hm.
- exact: borel_regularised_measure_borel_regular hm hb.
- move=> K hK.
  have hKb := closed_borel_set (compact_closed
    (@metric_hausdorff R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) hK).
  rewrite (borel_regularised_measure_borel_value hm hKb).
  exact (@convex_geometric_product_slice_compact_finite R m n k hKN V hV K hK).
- move=> a; apply: funext=> A; rewrite /measure_pushforward.
  have htrans z B : gamma ((fun x=>z+x) @` B)=gamma B.
    exact (@convex_geometric_product_slice_translation R m n k hKN z B V).
  have hi B := @borel_regularisation_invariant_bijection R
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] gamma
    (fun x=> -a+x) (fun x=>a+x)
    (fun x=>addNKr a x) (fun x=>addKr a x)
    (@euclidean_translation_continuous R m (-a)) (@euclidean_translation_continuous R m a)
    (htrans (-a)) B.
  have he : (fun x=>a+x) @^-1` A=(fun x=> -a+x) @` A.
    apply/seteqP; split=> x.
    + move=> hx; exists (a+x)=> //; by rewrite addKr.
    + move=> [y hy <-]; by rewrite /= addNKr.
  by rewrite he hi.
Qed.
