(** Supporting unchanged-closure gauge for Federer (1969), 2.10.3, p. 172,
    compact covering alternative. Continuity of the finite endpoint norm
    extends each finite upper bound from a set to its closure, one endpoint
    at a time. Finite and infinite suprema are treated through the abstract
    laws. This intermediate statement is not separately printed in the book. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  ExteriorDiameterUP ExteriorDiameterLaws ExteriorDiameter ExteriorEndpointContinuity
  ExteriorMeasureGauge FiniteCoordinateClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Import ArrowAsProduct.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_exterior_diameter_closure]: supporting
    closure invariance of the supremum in Federer
    2.10.3, p. 172. It justifies compact closure
    replacement at finite cutoffs. No boundedness or
    attainment hypothesis is needed for the identity. *)
Theorem extended_exterior_diameter_closure (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  extended_exterior_diameter m (closure A)=extended_exterior_diameter m A.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  exact (@extended_exterior_diameter_mono R n m A (closure A)
    (@subset_closure (inner_metric_space (@euclidean_inner_productP R n)) A)).
have hd := extended_exterior_diameter_specification m A.
have h0 := exterior_diameter_nonnegative hd.
apply: (exterior_diameter_least_bound (extended_exterior_diameter_specification m (closure A)) h0).
move=> a b ha hb.
case he: (extended_exterior_diameter m A) hd h0=> [q| |] hd h0.
- rewrite lee_fin.
  pose F := fun p : ('I_m*bool)%type -> inner_metric_space (@euclidean_inner_productP R n) =>
    (paired_exterior_norm p : RealMetricBackground.real_line_metric R).
  have hbase p : (forall i, A (p i)) -> (F p<=q)%R.
    move=> hp; have hh := exterior_diameter_endpoint_upper hd
      (fun i => hp (i,false)) (fun i => hp (i,true)).
    by move: hh; rewrite lee_fin.
  pose p (i : ('I_m*bool)%type) := if i.2 then b i.1 else a i.1.
  have hp i : closure A (p i) by case: i=> i e; case: e=> /=; [exact: hb|exact: ha].
  exact (@continuous_finite_coordinate_closure_bound R
    (inner_metric_space (@euclidean_inner_productP R n)) [the finType of ('I_m*bool)%type]
    F A q (@paired_exterior_norm_continuous R n m) hbase p hp).
- exact: leey.
- by [].
Qed.

(** Source for [exterior_diameter_cost_closure]: supporting
    unchanged normalized cost under closure for the
    compact-cover alternative of Federer 2.10.3, p. 172.
    Infinite values and the auxiliary empty-set convention
    are preserved. *)
Theorem exterior_diameter_cost_closure (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  exterior_diameter_cost m (closure A)=exterior_diameter_cost m A.
Proof. by rewrite /exterior_diameter_cost extended_exterior_diameter_closure. Qed.
