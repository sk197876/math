(** Federer (1969), 2.10.8, p. 175: small-diameter Borel partitions of an
    arbitrary Borel target in a separable metric space. The existence
    follows by intersecting the already sealed small partition with the
    target. This is supporting infrastructure, not a separately printed
    claim. Empty pieces and empty ambient spaces are allowed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import TopologicalBorel BorelFamilyBasic BorelPartition
  SmallBorelPartitionUP SmallBorelPartitionSealed MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [small_borel_partition_family_exists]: supporting
    existence of the arbitrarily fine Borel partitions used in
    Federer 2.10.8, p. 175. A countable dense subset expresses
    separability; no inhabitedness or finite-measure premise is added. *)
Theorem small_borel_partition_family_exists (R : realType) (X : metricType R)
    (D A : set X) (e : R) :
  countable D -> dense D -> borel_set A -> (0<e)%R ->
  exists H : set (set X), is_borel_partition A H /\
    forall B, H B -> extended_metric_diameter B<=e%:E.
Proof.
move=> hD hden hA he.
pose P := @SmallBorelPartition.value R X D e hD hden he.
have hP := @SmallBorelPartition.laws R X D e hD hden he.
pose F n := A `&` P n.
pose H := F @` setT.
exists H; split.
- constructor.
  + exact: sub_countable (card_image_le F setT) (@countableP nat setT).
  + move=> B C [i _ <-] [j _ <-] hne.
    have hij : i!=j by apply/eqP=> hij; apply: hne; by rewrite hij.
    apply/seteqP; split=> x; last by [].
    move=> [[_ hx] [_ hy]]; exact: (@small_partition_disjoint R X e P hP i j hij x hx hy).
  + move=> B [n _ <-]; exact: (@borel_family_binary_intersection X setT
      (@borel_set X) (borel_sets_family X) A (P n) hA (small_partition_borel hP n)).
  + apply/seteqP; split.
    * move=> x [B [n _ <-] [hx _]]; exact hx.
    * move=> x hx.
      have hall : (\bigcup_n P n) x by rewrite (small_partition_cover hP).
      have [n _ hn] := hall; exists (F n); first by exists n.
      by split.
- move=> B [n _ <-].
  apply: (metric_diameter_least (extended_metric_diameter_specification (F n))).
  + rewrite lee_fin; exact: ltW he.
  + move=> x y [_ hx] [_ hy]; rewrite lee_fin.
    exact: (@small_partition_diameter R X e P hP n x y hx hy).
Qed.
