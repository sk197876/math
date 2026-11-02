(** Federer (1969), 2.9.19, p. 165: refine a finite partition to arbitrarily
    small mesh without decreasing its length sum. Each original cell is
    replaced by a fine subdivision; the metric triangle inequality controls
    its old length. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import CurveVariationUP FineVariationPartitionUP FineVariationPartitionJoin
  UniformVariationPartitions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [fine_chain_refinement_exists]: supporting finite refinement
    in Federer 2.9.19, p. 165 Any nonempty nondecreasing chain has a fine
    partition with the same endpoints and at least its old metric length.
    Joining subdivisions inserts repeated endpoints, of zero additional
    length. Even an old singleton admits a degenerate two-endpoint
    partition. *)
Lemma fine_chain_refinement_exists (R : realType) (Y : metricType R)
    (g : R -> Y) (d : R) : 0<d -> forall s : seq R,
  s<>[::] -> sorted <=%O s -> exists t : seq R,
    is_variation_partition (head 0 s) (last 0 s) t /\
    variation_partition_mesh_lt d t /\ chain_sum g s<=chain_sum g t.
Proof.
move=> hd; elim=> [//|a [|b rest] ih] hne hs.
- have [t [ht hm]] := @fine_variation_partition_exists R a a d (lexx _) hd.
  exists t; split; first exact ht.
  split; first exact hm.
  exact: chain_sum_nonnegative.
- have /andP [hab hrest] : (a<=b) && sorted <=%O (b::rest) := hs.
  have [q [hq [hmq hlenq]]] := ih (ltac:(by [])) hrest.
  have [p [hp hmp]] := @fine_variation_partition_exists R a b d hab hd.
  exists (p++q); split; first exact: variation_partition_concat hp hq.
  split.
  + have [_ [hnp _]] := hp; have [_ [hnq _]] := hq.
    have hnep : p<>[::] by move=> heq; rewrite heq in hnp.
    have hneq : q<>[::] by move=> heq; rewrite heq in hnq.
    have [_ hlast] := variation_partition_zero_endpoints hp.
    have [hhead _] := variation_partition_zero_endpoints hq.
    apply: variation_partition_mesh_cat hnep hneq hmp hmq _.
    by rewrite hlast hhead subrr.
  + have [hhead hlast] := variation_partition_zero_endpoints hp.
    have hdist := @chain_sum_ge_endpoint_distance R Y g p 0.
    rewrite hhead hlast in hdist.
    rewrite (@variation_partition_chain_concat R Y g a b (last 0 (b::rest)) p q hp hq).
    exact: lerD hdist hlenq.
Qed.

(** Source for [fine_variation_partition_refinement]: supporting refinement
    of the actual variation partition in Federer 2.9.19, p. 165 The new
    partition retains a,b, has mesh below the prescribed positive d, and its
    length sum does not decrease. *)
Lemma fine_variation_partition_refinement (R : realType) (Y : metricType R)
    (g : R -> Y) (a b d : R) (s : seq R) : 0<d ->
  is_variation_partition a b s -> exists t : seq R,
    is_variation_partition a b t /\ variation_partition_mesh_lt d t /\
    chain_sum g s<=chain_sum g t.
Proof.
move=> hd hs; have [_ [hn _]] := hs.
have hne : s<>[::] by move=> heq; rewrite heq in hn.
have [t [ht [hm hlen]]] := @fine_chain_refinement_exists R Y g d hd s hne hs.1.
have [hh hl] := variation_partition_zero_endpoints hs.
rewrite hh hl in ht; exists t; by split=> //; split.
Qed.
