(** The complete product upper inequality in Federer (1969),
    3.2.45, p. 280, with the ordinary partial-product
    convention of 2.1.1, p. 51. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanCartesianMap
  EuclideanLebesgueDimensions IntegralGeometricMeasure ConvexGeometricProductUpperBound
  MeasureUP ExtendedRealPartial ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gillespie_euclidean_product_upper]: direct
    upper half of the product equality in Federer
    3.2.45, p. 280. Both original factors
    are arbitrary, and the second mass may be
    infinite. The original ordinary product must be
    defined, as in 2.1.1, p. 51.
    The finite case uses the proved cube-cover
    estimate; an infinite second mass makes the
    defined right member infinite. This stronger upper
    assertion needs no measurability of the first
    factor. The section inequality and product lower
    bound remain separate obligations. *)
Theorem gillespie_euclidean_product_upper (R : realType) m n k (hKN : (k <= n)%N)
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  mule_def (@euclidean_lebesgue_measure R m U)
    (@convex_integral_geometric_measure R n k hKN 1 V) ->
  @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
    (euclidean_cartesian_set U V) <=
      @euclidean_lebesgue_measure R m U * @convex_integral_geometric_measure R n k hKN 1 V.
Proof.
move=> hDefined.
case: (ltP (@convex_integral_geometric_measure R n k hKN 1 V) +oo)=> [hFinite|hInfinite].
- exact: convex_geometric_euclidean_product_upper_bound hFinite.
- have hInfinity : @convex_integral_geometric_measure R n k hKN 1 V = +oo.
    by apply/eqP; rewrite eq_le leey hInfinite.
  have hFirstNonzero : @euclidean_lebesgue_measure R m U != 0.
    apply/eqP=> hZero.
    by move: hDefined; rewrite hInfinity hZero /mule_def /= eqxx.
  have hFirstPositive : 0 < @euclidean_lebesgue_measure R m U.
    have hNonnegative := @measure_nonnegative R _ _ (euclidean_lebesgue_is_measure R m) U.
    by rewrite lt_def hFirstNonzero hNonnegative.
  rewrite hInfinity (gt0_muley hFirstPositive).
  exact: leey.
Qed.
