(** Federer (1969), 2.9.20, p. 166: the epsilon bound for finite increment
    sums also bounds variation on short subintervals. The proof uses the
    abstract variation supremum; no maximizing partition or prior
    bounded-variation hypothesis is imposed. Source context:
    RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP ExtendedRealBounds
  OrderedIntervalFamilyUP RealPartitionIntervalFamilies RealAbsoluteContinuityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_family_increment_bound_variation]: supporting first
    consequent implication of (3) in Federer 2.9.20, p. 166 Every variation
    partition of [u,v] yields an eligible strict family of total length v-u,
    including when partition terms repeat. Taking the supremum gives the
    same epsilon bound for V_u^v g. *)
Lemma real_family_increment_bound_variation (R : realType) (g : R -> R)
    (a b d e u v : R) :
  (forall s : seq (R * R), is_ordered_real_interval_family a b s ->
    real_interval_family_length s<=d -> real_interval_family_increment_sum g s<=e) ->
  a<=u -> u<=v -> v<=b -> v-u<=d ->
  (curve_variation (g : R -> real_line_metric R) u v<=e%:E)%E.
Proof.
move=> hfamily hau huv hvb hwidth.
apply: extended_real_sup_least=> z [s [[hs [hn [hh hl]]] ->]].
have hordered : is_ordered_real_interval_family a b (real_partition_interval_cells s).
  apply: real_partition_cells_ordered hs _ _.
  + have he : head a s=head u s by case: s hn hh hl=> [//|p s'].
    by rewrite he hh.
  + have he : last a s=last u s by case: s hn hh hl=> [//|p s'].
    by rewrite he hl.
have hlen : real_interval_family_length (real_partition_interval_cells s)<=d.
  by rewrite (@real_partition_cells_length R s u hs) hh hl.
have hb := hfamily _ hordered hlen.
by rewrite (@real_partition_cells_increments R g s hs) in hb; rewrite lee_fin.
Qed.

(** Source for [real_absolute_continuity_small_variation]: supporting
    short-interval consequence of Federer 2.9.20(3), p. 166 Absolute
    continuity supplies a uniform bound on total variation over every
    sufficiently short subinterval. This proves finiteness on those
    subintervals without a separate bounded-variation assumption. *)
Theorem real_absolute_continuity_small_variation (R : realType) (g : R -> R)
    (a b : R) : is_absolutely_continuous_real_curve g a b ->
  forall e : R, 0<e -> exists d : R, 0<d /\ forall u v : R,
    a<=u -> u<=v -> v<=b -> v-u<=d ->
    (curve_variation (g : R -> real_line_metric R) u v<=e%:E)%E.
Proof.
move=> hg e he; have [d [hd hs]] := hg e he.
exists d; split=> // u v hau huv hvb hwidth.
exact: real_family_increment_bound_variation hs hau huv hvb hwidth.
Qed.
