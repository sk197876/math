(** Finite interval cuts for the rectangular packing supporting
    Federer (1969), 2.8.20, p. 152. The finite
    decompositions in Saks1934 Lemma B, p. 258, and
    Cesari1939 Lemma III, p. 306, require disjoint
    remaining rectangular regions. Cutting at the two endpoints
    of a half-open interval gives three regions. These are
    auxiliary set-theoretic lemmas, not separately stated claims
    in Federer. Exact source titles: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [interval_cut_region]: the three possible
    positions relative to a removed interval, supporting the
    finite rectangular decompositions for Federer 2.8.20,
    p. 152. None is the middle region; Some false
    and Some true are the lower and upper regions. *)
Definition interval_cut_region (R : realType) (u v : R) (tag : option bool) (x : R) :=
  match tag with None => u <= x < v | Some false => x < u | Some true => v <= x end.

(** Source for [interval_cut_region_exists]: supporting point
    coverage by the three regions in the finite construction
    for Federer 2.8.20, p. 152. The middle
    interval is nondegenerate; no endpoint is omitted. *)
Lemma interval_cut_region_exists (R : realType) (u v x : R) :
  u < v -> exists tag, interval_cut_region u v tag x.
Proof.
move=> huv; case: (ltP x u)=> hxu.
- by exists (Some false).
- case: (ltP x v)=> hxv; last by exists (Some true).
  by exists None; rewrite /interval_cut_region hxu hxv.
Qed.

(** Source for [interval_cut_region_unique]: supporting
    disjointness of the three regions in the finite rectangle
    construction for Federer 2.8.20, p. 152. *)
Lemma interval_cut_region_unique (R : realType) (u v x : R) (s t : option bool) :
  u < v -> interval_cut_region u v s x -> interval_cut_region u v t x -> s = t.
Proof.
move=> huv hs ht.
case: s hs=> [[|]|] hs; case: t ht=> [[|]|] ht=> //.
all: rewrite /interval_cut_region /= in hs.
all: rewrite /interval_cut_region /= in ht.
all: try (move/andP: hs=> [hs1 hs2]).
all: try (move/andP: ht=> [ht1 ht2]).
all: exfalso; lra.
Qed.

(** Source for [interval_cut_lower_endpoint]: lower endpoint
    after intersecting a bounded interval with a region,
    supporting Federer 2.8.20, p. 152. Empty
    resulting intervals are allowed in the auxiliary partition. *)
Definition interval_cut_lower_endpoint (R : realType) (a u v : R) (tag : option bool) :=
  match tag with None => Num.max a u | Some false => a | Some true => Num.max a v end.

(** Source for [interval_cut_upper_endpoint]: upper endpoint
    of the auxiliary intersection interval supporting Federer
    2.8.20, p. 152. *)
Definition interval_cut_upper_endpoint (R : realType) (b u v : R) (tag : option bool) :=
  match tag with None => Num.min b v | Some false => Num.min b u | Some true => b end.

(** Source for [interval_cut_cellE]: supporting interval
    intersection formula for the finite rectangular decomposition
    in Federer 2.8.20, p. 152. It holds even
    when the original or resulting bounded interval is empty. *)
Lemma interval_cut_cellE (R : realType) (a b u v x : R) (tag : option bool) :
  (x \in Interval (BLeft (interval_cut_lower_endpoint a u v tag)) (BLeft (interval_cut_upper_endpoint b u v tag))) =
  (x \in Interval (BLeft a) (BLeft b)) && interval_cut_region u v tag x.
Proof.
case: tag=> [[|]|]; rewrite /interval_cut_lower_endpoint /interval_cut_upper_endpoint
  /interval_cut_region /= !in_itv /= ?ge_max ?lt_min.
- by rewrite andbAC.
- by rewrite andbA.
- by rewrite andbACA.
Qed.
