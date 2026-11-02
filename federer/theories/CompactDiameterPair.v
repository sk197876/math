(** Federer (1969), 2.10.38, printed p. 199: choose a first pair in the
    nonempty compact source whose distance is its diameter. This supporting
    maximum theorem is valid in every metric space, by compactness of the
    product and continuity of pair distance. The target book statement on p.
    198 needs a nonempty source in positive dimension; this qualification is
    separate from Federer's working erratum, which has no entry for pp.
    198–199. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactMaximum MetricPairDistance MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_metric_diameter_pair]: supporting
    attained first chord in 2.10.38,
    p. 199. The actual sealed diameter is
    identified with the distance of the selected
    pair, and its pairwise upper bound is retained. *)
Theorem compact_metric_diameter_pair (R : realType) (X : metricType R) (S : set X) :
  compact S -> S !=set0 -> exists a b,
    S a /\ S b /\ extended_metric_diameter S=(mdist a b)%:E /\
    forall x y, S x -> S y -> mdist x y<=mdist a b.
Proof.
move=> hS [a ha].
have hne : S `*` S !=set0 by exists (a,a); split.
have hc : compact (S `*` S) := compact_setX hS hS.
have [p [[hp1 hp2] hmax]] := @continuous_compact_maximum R
  [the topologicalType of (X*X)%type] (S `*` S) (fun p=>(mdist p.1 p.2 : R^o))
  hne hc (@metric_pair_distance_continuous R X).
have hbound x y : S x -> S y -> mdist x y<=mdist p.1 p.2.
  move=> hx hy; exact: hmax (x,y) (conj hx hy).
exists p.1,p.2; split=> //; split=> //; split=> //.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (metric_diameter_least (extended_metric_diameter_specification S)).
  + by rewrite lee_fin; exact: mdist_ge0.
  + by move=> x y hx hy; rewrite lee_fin; exact: hbound.
- exact (@metric_diameter_upper R X S (extended_metric_diameter S)
    (extended_metric_diameter_specification S) p.1 p.2 hp1 hp2).
Qed.
