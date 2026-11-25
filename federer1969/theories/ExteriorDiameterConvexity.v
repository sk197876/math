(** Federer (1969), 2.10.3, p. 172: any set and its convex hull receive the
    same cost because the exterior endpoint map is separately affine in its
    2m variables. Apply the proved finite-coordinate hull bound to the
    actual exterior norm, then use the supremum's least-upper-bound laws.
    Source context: ExteriorDiameterUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerNormInequalities
  ExteriorGrading ExteriorNorm RealNormUP ConvexHull
  SeparateAffineHullBound ExteriorEndpointAffinity ExteriorDiameterUP ExteriorDiameterLaws
  ExteriorDiameter ExteriorMeasureGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [exterior_endpoint_norm_hull_bound]: supporting
    bounded-sublevel version of the printed separate-affinity
    argument in Federer 2.10.3, p. 172. No attained
    supremum, closed source set or dimension restriction
    on the degree is required. *)
Lemma exterior_endpoint_norm_hull_bound (R : realType) (n m : nat)
    (A : set (R_n R n)) (q : R) :
  (forall a b : 'I_m -> R_n R n, (forall i, A (a i)) -> (forall i, A (b i)) ->
    exterior_difference_norm a b<=q) ->
  forall a b : 'I_m -> R_n R n,
    (forall i, convex_hull A (a i)) -> (forall i, convex_hull A (b i)) ->
    exterior_difference_norm a b<=q.
Proof.
move=> hA a b ha hb.
pose N := @exterior_norm R (real_exterior_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m.
have hN : is_real_norm N.
  split.
  - split.
    + exact: exterior_norm_nonnegative.
    + by move=> c x; exact: exterior_norm_scale.
    + move=> x y; exact: inner_norm_triangle.
  - move=> x hx; rewrite /N in hx; apply/eqP.
    by rewrite -(@exterior_norm_eq0 R (real_exterior_two_nonzero R) (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m x) hx eqxx.
pose F := @paired_exterior_product R (R_n R n) m.
have hF p i : AffineMaps.is_affine_map (fun x => F (coordinate_replacement p i x)).
  exact: paired_exterior_product_separately_affine.
have hbase p : (forall i, A (p i)) -> N (F p)<=q.
  move=> hp; exact (hA (fun i => p (i,false)) (fun i => p (i,true))
    (fun i => hp (i,false)) (fun i => hp (i,true))).
pose p (i : ('I_m*bool)%type) := if i.2 then b i.1 else a i.1.
have hp i : convex_hull A (p i) by case: i=> i e; case: e=> /=; [exact: hb|exact: ha].
have hh := @separately_affine_norm_bound_convex_hull R [the finType of ('I_m*bool)%type]
  (R_n R n) (exterior_power (R_n R n) m) F N hN A q hF hbase p hp.
exact hh.
Qed.

(** Source for [extended_exterior_diameter_convex_hull]:
    direct unchanged-supremum assertion of Federer 2.10.3,
    p. 172. Finite and infinite values are included;
    the auxiliary empty-set convention is also preserved. *)
Theorem extended_exterior_diameter_convex_hull (R : realType) (n m : nat)
    (A : set (R_n R n)) :
  extended_exterior_diameter m (convex_hull A)=extended_exterior_diameter m A.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  exact (@extended_exterior_diameter_mono R n m A (convex_hull A)
    (@convex_hull_includes R (R_n R n) A)).
have hd := extended_exterior_diameter_specification m A.
have h0 := exterior_diameter_nonnegative hd.
apply: (exterior_diameter_least_bound (extended_exterior_diameter_specification m (convex_hull A)) h0).
move=> a b ha hb.
case he: (extended_exterior_diameter m A) hd h0=> [q| |] hd h0.
- rewrite lee_fin; apply: (@exterior_endpoint_norm_hull_bound R n m A q _ a b ha hb).
  move=> u v hu hv; have hh := exterior_diameter_endpoint_upper hd hu hv.
  by move: hh; rewrite lee_fin.
- exact: leey.
- by [].
Qed.

(** Source for [exterior_diameter_cost_convex_hull]: direct
    unchanged-cost assertion of Federer 2.10.3, p. 172,
    with the printed normalization factor retained. *)
Theorem exterior_diameter_cost_convex_hull (R : realType) (n m : nat) (A : set (R_n R n)) :
  exterior_diameter_cost m (convex_hull A)=exterior_diameter_cost m A.
Proof. by rewrite /exterior_diameter_cost extended_exterior_diameter_convex_hull. Qed.
