(** Federer (1969), 2.9.20, p. 166, the first consequent implication of (3):
    refine intervals by variation partitions. The existing partitions of
    2.5.16 allow repeated terms; this adapter discards zero-width cells so
    that the strict family convention of 2.9.20(3) is preserved. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP OrderedIntervalFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_partition_interval_cells]: supporting finite refinement
    of the intervals in Federer 2.9.20(3), p. 166 Retain exactly the
    strictly positive adjacent cells of a sorted partition. This
    construction only supplies a witness for the family laws. *)
Fixpoint real_partition_interval_cells (R : realType) (s : seq R) : seq (R * R) :=
  match s with
  | t :: ((u :: _) as rest) =>
      if t<u then (t,u) :: real_partition_interval_cells rest
      else real_partition_interval_cells rest
  | _ => [::]
  end.

(** Source for [real_partition_cells_ordered]: supporting family
    eligibility in Federer 2.9.20, p. 166. Nondecreasing partition
    terms bounded by a and b yield an eligible strict interval family. *)
Lemma real_partition_cells_ordered (R : realType) (s : seq R) (a b : R) :
  sorted <=%O s -> a<=head a s -> last a s<=b ->
  is_ordered_real_interval_family a b (real_partition_interval_cells s).
Proof.
elim: s a=> [|t [|u rest] ih] a //= /andP[htu hs] hat hlb.
have hul : u<=last u rest.
  have := @sorted_le_last R (u::rest) u u hs (mem_head u rest); by rewrite /=.
have hub : u<=b := le_trans hul hlb.
case: ifP=> htu'.
- split=> //; split=> //; split=> //.
  exact: ih hs (lexx u) hlb.
- apply: ih hs _ hlb; exact: le_trans hat htu.
Qed.

(** Source for [real_partition_cells_length]: supporting preservation of
    total interval length under refinement in Federer 2.9.20, p. 166
    Repeated partition terms contribute zero, so deleting their degenerate
    cells leaves exactly last(s)-head(s). *)
Lemma real_partition_cells_length (R : realType) (s : seq R) (a : R) :
  sorted <=%O s -> real_interval_family_length (real_partition_interval_cells s)=
    last a s-head a s.
Proof.
elim: s a=> [|t [|u rest] ih] a /= hs.
- by rewrite /real_interval_family_length big_nil subrr.
- by rewrite /real_interval_family_length big_nil subrr.
- have /andP[htu hs'] := hs.
  case: ifP=> htu'.
  + rewrite /real_interval_family_length big_cons.
    change ((u-t)+real_interval_family_length (real_partition_interval_cells (u::rest))=
      last u rest-t).
    rewrite (ih u hs').
    by rewrite addrC addrA subrK.
  + change (real_interval_family_length (real_partition_interval_cells (u::rest))=
      last u rest-t).
    have htuE : t=u by apply/eqP; rewrite eq_le htu leNgt htu'.
    by rewrite (ih u hs') htuE.
Qed.

(** Source for [real_partition_cells_increments]: supporting exact passage
    from partition lengths to the sum in condition (3), Federer 2.9.20, p.
    166 Zero-width cells have zero increment even when g is discontinuous,
    so no regularity hypothesis is needed. *)
Lemma real_partition_cells_increments (R : realType) (g : R -> R) (s : seq R) :
  sorted <=%O s ->
  real_interval_family_increment_sum g (real_partition_interval_cells s)=
    chain_sum (g : R -> real_line_metric R) s.
Proof.
elim: s=> [|t [|u rest] ih] /= hs; try by rewrite /real_interval_family_increment_sum big_nil.
have /andP[htu hs'] := hs.
case: ifP=> htu'.
- rewrite /real_interval_family_increment_sum big_cons.
  change (`|g u-g t|+real_interval_family_increment_sum g
    (real_partition_interval_cells (u::rest))=
    mdist (g t : real_line_metric R) (g u)+chain_sum (g : R -> real_line_metric R) (u::rest)).
  rewrite (ih hs') real_line_metric_distanceE.
  by rewrite distrC.
- change (real_interval_family_increment_sum g (real_partition_interval_cells (u::rest))=
    mdist (g t : real_line_metric R) (g u)+chain_sum (g : R -> real_line_metric R) (u::rest)).
  have htuE : t=u by apply/eqP; rewrite eq_le htu leNgt htu'.
  by rewrite (ih hs') htuE real_line_metric_distanceE subrr normr0 add0r.
Qed.
