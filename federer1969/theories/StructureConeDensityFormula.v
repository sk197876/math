(** Federer (1969), 3.3.2, p. 287: identify the independently
    sealed density with the literal printed upper limit of radius
    suprema. This order comparison uses every positive aperture
    cutoff and does not assume any measurability result. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  ExtendedRealBoundsUP ExtendedRealBounds PositiveRadiusLimits
  StructureConeDensityUP StructureConeDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_cone_radial_supremum]: the inner
    supremum over 0<r<delta in Federer 3.3.2, p. 287.
    This is an application of the already sealed extended
    supremum operator to the original normalized cone masses. *)
Definition structure_cone_radial_supremum (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (delta:R) z (s:R):=
  extended_real_sup [set v|exists r:R,
    (0<r<delta) /\ v=structure_cone_cost hmn phi A z r s].

(** Source for [structure_cone_iterated_tail_laws]: supporting
    interchange of the two suprema in Federer 3.3.2,
    pp. 287–288. Prove both independent least-upper-bound
    laws; no finite-mass or attained-supremum premise is added. *)
Lemma structure_cone_iterated_tail_laws (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (delta:R) z (t:R):
  is_structure_cone_tail_supremum hmn phi A delta z t
    (extended_real_sup (positive_radius_values
      (structure_cone_radial_supremum hmn phi A delta z) t)).
Proof.
constructor.
- move=>v [r [s [hr [hs ->]]]].
  have hInner:(structure_cone_cost hmn phi A z r s<=
      structure_cone_radial_supremum hmn phi A delta z s)%E.
    apply:extended_real_sup_upper; by exists r.
  apply:le_trans hInner _; apply:extended_real_sup_upper.
  by exists s.
- move=>b hBound; apply:extended_real_sup_least=>v [s [hs ->]].
  apply:extended_real_sup_least=>w [r [hr ->]]; apply:hBound.
  by exists r,s.
Qed.

(** Source for [structure_cone_density_bookE]: the literal
    limsup_(s to 0+) sup_(0<r<delta) expression in Federer
    3.3.2, p. 287, equals the independently specified
    sealed density. All positive real scales and either
    infinite value are retained. *)
Theorem structure_cone_density_bookE (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (delta:R) z:
  structure_cone_density hmn phi A delta z=
    positive_radius_upper_limit (structure_cone_radial_supremum hmn phi A delta z).
Proof.
have h:=@structure_cone_density_specification R n m hmn phi A delta z.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply:extended_real_inf_greatest=>q [t [ht ->]].
  exact:(h.1 t _ ht (structure_cone_iterated_tail_laws hmn phi A delta z t)).
- apply:h.2=>t q ht hq.
  have he:q=extended_real_sup (positive_radius_values
      (structure_cone_radial_supremum hmn phi A delta z) t).
    exact:(extended_real_supremum_unique hq
      (structure_cone_iterated_tail_laws hmn phi A delta z t)).
  rewrite he; apply:extended_real_inf_lower; by exists t.
Qed.
