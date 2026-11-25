(** Supporting convex projection geometry for Federer (1969), 2.10.5(2), p.
    173, and the forward continuity reference 3.2.36, p. 272. A convex
    source with positive volume under one projection contains a translated
    small ball along an actual linear right inverse of that projection.
    Positive projected volume supplies a difference basis; choose actual
    preimages and place the buffer at their simplex barycentre. Thus the
    basis and interior premises are discharged, rather than added to the
    target hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace ProjectedVolumeMeasurability InnerConvex
  PositiveVolumeAffineSpan ConvexProjectionSectionBuffer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_projected_volume_convex_buffer]:
    supporting local lifting buffer for the compact
    convex continuity behind Federer 2.10.5(2),
    p. 173, and 3.2.36, p. 272. This
    existence step needs convexity and positive
    projected volume, but not compactness. *)
Theorem positive_projected_volume_convex_buffer (R : realType) (n m : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : euclidean_projection_space R n m) (a : R_n R n) :
  is_inner_convex K -> K a -> (0<projected_volume_function K p)%E ->
  exists (b : R_n R n) (g : {linear R_n R m -> R_n R n}) (r : R),
    K b /\ cancel g (euclidean_projection_linear p) /\ 0<r /\
    forall u : inner_metric_space (@euclidean_inner_productP R m),
      mdist (0%R : inner_metric_space (@euclidean_inner_productP R m)) u<r -> K (b+g u).
Proof.
move=> hK ha hpos.
pose S := euclidean_projection_linear p @` K.
have hpa : S (euclidean_projection_linear p a) by exists a.
have [e [he hpts]] := @euclidean_positive_volume_difference_basis R m S
  (euclidean_projection_linear p a) hpa hpos.
have hex i : exists x, K x /\ euclidean_projection_linear p x=e i+euclidean_projection_linear p a.
  have [x hx heq] := hpts i; exists x; by split.
pose x i := projT1 (cid (hex i)).
have hx i : K (x i) /\ euclidean_projection_linear p (x i)=e i+euclidean_projection_linear p a.
  exact: projT2 (cid (hex i)).
pose v i := x i-a.
have hv i : K (a+v i) by rewrite /v addrC subrK; exact: (hx i).1.
have hpv i : euclidean_projection_linear p (v i)=e i.
  by rewrite /v linearB (hx i).2 addrK.
exact: (@convex_projection_section_buffer R n m K (euclidean_projection_linear p)
  a v e hK ha hv he hpv).
Qed.
