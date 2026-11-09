(** Federer (1969), 3.4.4, p. 318: independent
    laws of the map induced by corresponding original intervals. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_binary_cantor_correspondence]: the original
    interval correspondence inducing phi in 3.4.4, p. 318.
    The map takes the original source into the original target
    and respects every finite interval address. Continuity, inverse
    identities, order, and Holder estimates are subsequent theorems. *)
Record is_binary_cantor_correspondence (R:realType)
    (A B:set (real_line_metric R))
    (I J:seq bool->compact_real_intervals R) (phi:R->R):Prop:={
  (** Source for [binary_cantor_correspondence_maps]: phi maps
      the original A(alpha,n) into A(beta,n), 3.4.4, p. 318. *)
  binary_cantor_correspondence_maps:forall x,A x ->B (phi x);
  (** Source for [binary_cantor_correspondence_intervals]: matching
      original finite-level intervals determine the correspondence
      in 3.4.4, p. 318. Only source points in
      the original Cantor set have prescribed values. *)
  binary_cantor_correspondence_intervals:forall w x,A x ->
    val (I w) x ->val (J w) (phi x)
}.
