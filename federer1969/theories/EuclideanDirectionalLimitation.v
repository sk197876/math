(** Federer (1969), 2.9.18(2), p. 163, uses a directionally limited
    Euclidean metric. The finite-dimensional norm argument is Federer 2.8.9,
    p. 146. we retain Federer's original definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  InnerMetric InnerNormInequalities RealNormUP NormMetric DirectionalLimitationUP
  NormDirectionalLimitation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [euclidean_directional_limitation]: the
    Euclidean directional-limitation assertion in Federer
    2.9.18(2), p. 163, from 2.8.9, p. 146.
    The existing finite-dimensional norm result is transported
    across wrappers with definitionally identical distances,
    after verifying its norm hypotheses from the inner-norm laws.
    Every dimension, including dimension zero, is covered. *)
Theorem euclidean_directional_limitation (R : realType) n (eta : R) :
  0<eta<=1/3 -> exists zeta : nat,
    @is_directionally_limited_at R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT +oo%E eta zeta.
Proof.
move=> heta.
have hN : is_real_norm (inner_norm (@euclidean_inner_productP R n)).
  split.
  - split; [exact: inner_norm_nonnegative|exact: inner_normZ|exact: inner_norm_triangle].
  - move=> x hx; apply/eqP.
    by rewrite -(inner_norm_eq0 (@euclidean_inner_productP R n)) hx eqxx.
have [zeta hz] := @finite_norm_directional_limitation R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) hN n
  (@coordinate_basis R n) (@coordinate_basisP R n) eta heta.
exists zeta; constructor.
- exact: directional_radius_positive hz.
- exact: directional_separation_range hz.
- exact: directional_cardinal_positive hz.
- move=> a ha B hB hs.
  exact (@directional_cardinal_bound R
    [the metricType R of real_norm_metric_space hN] setT +oo%E eta zeta hz a ha B hB hs).
Qed.
