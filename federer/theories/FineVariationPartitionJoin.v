(** Federer (1969), 2.9.19, p. 165: refinement and concatenation of finite
    variation partitions. These finite-chain lemmas support its existence
    and preserve the original length sum under refinement. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import CurveVariationUP FineVariationPartitionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [variation_partition_zero_endpoints]: supporting endpoint
    extraction for the finite partitions in Federer 2.9.19, p. 165
    Nonemptiness makes the head/last default immaterial, so default zero
    recovers the specified endpoints a,b. *)
Lemma variation_partition_zero_endpoints (R : realType) (a b : R) (s : seq R) :
  is_variation_partition a b s -> head 0 s=a /\ last 0 s=b.
Proof.
case: s=> [|t rest] [_ [hn [hh hl]]]; first by [].
by split.
Qed.

(** Source for [variation_partition_mesh_cat]: supporting mesh preservation
    in the refinement of Federer 2.9.19, p. 165 A concatenation is fine if
    both chains and their joining gap are fine. *)
Lemma variation_partition_mesh_cat (R : realType) (d : R) (s t : seq R) :
  s<>[::] -> t<>[::] -> variation_partition_mesh_lt d s -> variation_partition_mesh_lt d t ->
  head 0 t-last 0 s<d -> variation_partition_mesh_lt d (s++t).
Proof.
elim: s=> [//|a [|b rest] ih] hs ht hS hT hgap.
- clear ih; case: t ht hT hgap=> [//|c ts] _ hT hgap.
  change (is_true ((c-a<d) && variation_partition_mesh_lt d (c::ts))).
  apply/andP; split; [exact hgap|exact hT].
- move: hS=> /andP [hab hrest]; rewrite /= hab /=.
  apply: ih=> //.
Qed.

(** Source for [variation_partition_concat]: supporting refinement
    concatenation in Federer 2.9.19, p. 165 Join two nondecreasing
    partitions with a common endpoint. The repeated joining point is allowed
    by the existing partition representation and adds zero length. *)
Lemma variation_partition_concat (R : realType) (a b c : R) (s t : seq R) :
  is_variation_partition a b s -> is_variation_partition b c t ->
  is_variation_partition a c (s++t).
Proof.
move=> hS hT; have [hs [hns [hhs hls]]] := hS.
have [ht [hnt [hht hlt]]] := hT.
have hneS : s<>[::] by move=> h; rewrite h in hns.
have hneT : t<>[::] by move=> h; rewrite h in hnt.
split.
- apply: sorted_cat_le=> // x y hx hy.
  have hxb := (andP (variation_partition_bounds hS hx)).2.
  have hby := (andP (variation_partition_bounds hT hy)).1.
  exact: le_trans hxb hby.
- split; first by rewrite size_cat; exact: leq_trans hns (leq_addr _ _).
  split.
  + by case: s hneS hhs {hS hs hns hls}=> [//|u rest] _ /= ->.
  + rewrite last_cat; by case: t hneT hlt {hT ht hnt hht}=> [//|u rest] _ /= ->.
Qed.

(** Source for [variation_partition_chain_concat]: supporting length
    additivity for the refinement in Federer 2.9.19, p. 165 The common
    joining endpoint contributes zero distance, so concatenated length is
    the sum of the two chain lengths in any metric target. *)
Lemma variation_partition_chain_concat (R : realType) (Y : metricType R)
    (g : R -> Y) (a b c : R) (s t : seq R) :
  is_variation_partition a b s -> is_variation_partition b c t ->
  chain_sum g (s++t)=chain_sum g s+chain_sum g t.
Proof.
move=> hS hT; have [_ [hns _]] := hS; have [_ [hnt _]] := hT.
have hneS : s<>[::] by move=> h; rewrite h in hns.
have hneT : t<>[::] by move=> h; rewrite h in hnt.
have [_ hlast] := variation_partition_zero_endpoints hS.
have [hhead _] := variation_partition_zero_endpoints hT.
by rewrite (@chain_sum_cat R Y g s t hneS hneT) hlast hhead mdistxx addr0.
Qed.
