(** Federer (1969), 2.9.19, p. 165: fine subdivisions used to refine a
    nearly maximal variation partition. The existence proof reuses the
    project's uniform subdivisions from 2.5.17, pp. 110–111, without making
    their formulas part of the downstream near-maximal partition
    specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import CurveVariationUP FineVariationPartitionUP StieltjesIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [uniform_variation_partition_mesh]: supporting uniform
    refinement for the partition choice in Federer 2.9.19, p. 165
    Consecutive entries in the existing left-tagged uniform subdivision
    differ by zero or by h. Both are below d. *)
Lemma uniform_variation_partition_mesh (R : realType) (h d : R) : 0<d -> h<d ->
  forall n a, variation_partition_mesh_lt d (@uniform_tagged R a h n).
Proof.
move=> hd hh; elim=> [//|n ih] a.
case: n ih=> [|n] ih /=.
- have heq : a+h-a=h by rewrite addrAC subrr add0r.
  by rewrite subrr hd heq hh.
- have heq : a+h-a=h by rewrite addrAC subrr add0r.
  rewrite subrr hd heq hh /=; exact: ih (a+h).
Qed.

(** Source for [fine_variation_partition_exists]: supporting arbitrarily
    fine subdivision in Federer 2.9.19, p. 165 Every finite real segment,
    including a degenerate segment, has a nondecreasing finite partition of
    mesh below any positive d. This gives existence; later proofs use only
    its laws. *)
Lemma fine_variation_partition_exists (R : realType) (a b d : R) : a<=b -> 0<d ->
  exists s : seq R, is_variation_partition a b s /\ variation_partition_mesh_lt d s.
Proof.
move=> hab hd.
have [N hN] := @uniform_mesh_small R a b d hab hd.
pose s := @uniform_partition R a b N.
have [hs [_ [hh hl]]] := @uniform_partition_is R a b N hab.
have hsize : (1<size s)%N.
  by rewrite /s /uniform_partition uniform_tagged_size ltnS muln_gt0.
exists s; split.
- by split=> //; split=> //; split.
- exact (@uniform_variation_partition_mesh R ((b-a)/(N.+1)%:R) d hd (hN N (leqnn N)) N.+1 a).
Qed.
