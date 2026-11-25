(** Exterior-diameter contraction in Federer (1969), 2.10.32, pp. 196–197.
    Pass from the checked endpoint estimate to the abstract extended
    supremum and then multiply by the positive normalising factor alpha(n)
    2^(-n). No finite or attained supremum is assumed. The distinction
    between this normalised cost and an endpoint norm is exactly the one
    required by Federer's erratum p. 4, book p. 197 line 4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  SteinerSymmetrisationUP SteinerExteriorDiameterBound ExteriorDiameterUP ExteriorDiameterLaws
  ExteriorDiameter ExteriorMeasureGauge HausdorffDiameterCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_top_exterior_diameter_bound]: direct
    unnormalised supremum contraction proved in
    2.10.32, pp. 196–197. The upper bound
    may be infinite; every finite endpoint bound
    is transported by the preceding norm theorem. *)
Theorem steiner_top_exterior_diameter_bound (R : realType) (n : nat)
    (u : R_n R n) (S T : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_steiner_symmetrisation (@euclidean_inner_productP R n) u S T -> compact S -> is_inner_convex S ->
  (extended_exterior_diameter n T<=extended_exterior_diameter n S)%E.
Proof.
move=> hs hc hconv.
have hdS := extended_exterior_diameter_specification n S.
have h0 := exterior_diameter_nonnegative hdS.
apply: (exterior_diameter_least_bound (extended_exterior_diameter_specification n T) h0).
move=> a b ha hb.
case he: (extended_exterior_diameter n S) hdS h0=> [M| |] hdS h0.
- rewrite lee_fin; apply: (steiner_top_exterior_endpoint_bound hs hc hconv _ ha hb).
  move=> x y hx hy.
  have hh := exterior_diameter_endpoint_upper hdS hx hy.
  by move: hh; rewrite lee_fin.
- exact: leey.
- by [].
Qed.

(** Source for [steiner_top_exterior_cost_bound]: direct
    preservation of the cost bound defining C
    in 2.10.32, pp. 196–197. Restore the
    printed alpha(n) 2^(-n) factor explicitly;
    no extra factor is dropped. *)
Theorem steiner_top_exterior_cost_bound (R : realType) (n : nat)
    (u : R_n R n) (S T : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_steiner_symmetrisation (@euclidean_inner_productP R n) u S T -> compact S -> is_inner_convex S ->
  (exterior_diameter_cost n T<=exterior_diameter_cost n S)%E.
Proof.
move=> hs hc hconv.
rewrite /exterior_diameter_cost; apply: lee_wpmul2l.
- rewrite lee_fin; exact: ltW (@hausdorff_normalisation_positive R n).
- exact (steiner_top_exterior_diameter_bound hs hc hconv).
Qed.
