(** Federer (1969), 2.10.29, p. 195: the orthogonal identification of
    A^q*B^q with (A*B)^q, using only the sealed coordinate regrouping laws.
    Both sides use the actual existing Euclidean spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanMeasurePowerUP EuclideanBlockSetPower EuclideanSetPowers EuclideanCantorProduct
  EuclideanPairPowerShuffleUP EuclideanPairPowerShuffleSealed EuclideanBlockCoordinates EuclideanMetricProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_pair_power_shuffle]: public
    abstract coordinate regrouping in 2.10.29,
    p. 195. Its implementation is opaque. *)
Definition euclidean_pair_power_shuffle (R : realType) q := @EuclideanPairPowerShuffle.value R q.

(** Source for [euclidean_pair_power_shuffle_specification]: direct
    proved orthogonal identification laws for
    2.10.29, p. 195, from the sealed interface. *)
Lemma euclidean_pair_power_shuffle_specification (R : realType) q :
  is_euclidean_pair_power_shuffle (@euclidean_pair_power_shuffle R q).
Proof. exact: EuclideanPairPowerShuffle.laws. Qed.

(** Source for [euclidean_power_product]: direct
    A^q*B^q in the actual Euclidean R^(q+q)
    of 2.10.29, p. 195, specified by
    the two block coordinate membership predicates. *)
Definition euclidean_power_product (R : realType) q (A B : set (real_line_metric R)) :
    set (inner_metric_space (@euclidean_inner_productP R (q+q))) :=
  [set x | euclidean_set_power q A (@euclidean_block_split R q q x).1 /\
    euclidean_set_power q B (@euclidean_block_split R q q x).2].

(** Source for [euclidean_power_regroup]: public
    forward orthogonal identification from the
    two scalar powers to the power of pairs
    in 2.10.29, p. 195. *)
Definition euclidean_power_regroup (R : realType) q
    (x : inner_metric_space (@euclidean_inner_productP R (q.+1+q.+1))) :=
  pair_power_shuffle_forward (@euclidean_pair_power_shuffle R q) (@euclidean_block_split R q.+1 q.+1 x).

(** Source for [euclidean_power_ungroup]: public
    inverse orthogonal identification in 2.10.29,
    p. 195. Both maps use only the
    sealed coordinate laws and existing block maps. *)
Definition euclidean_power_ungroup (R : realType) q
    (y : inner_metric_space (@euclidean_inner_productP R (euclidean_power_dimension 2 q))) :=
  @euclidean_block_join R q.+1 q.+1 (pair_power_shuffle_backward (@euclidean_pair_power_shuffle R q) y).

(** Source for [euclidean_power_regroupK]: supporting
    first inverse law of the actual
    Euclidean identification in 2.10.29, p. 195. *)
Lemma euclidean_power_regroupK (R : realType) q :
  cancel (@euclidean_power_regroup R q) (@euclidean_power_ungroup R q).
Proof.
move=> x; rewrite /euclidean_power_regroup /euclidean_power_ungroup
  (pair_power_shuffle_forwardK (@euclidean_pair_power_shuffle_specification R q)).
exact: euclidean_block_splitK.
Qed.

(** Source for [euclidean_power_ungroupK]: supporting
    second inverse law of the actual
    Euclidean identification in 2.10.29, p. 195. *)
Lemma euclidean_power_ungroupK (R : realType) q :
  cancel (@euclidean_power_ungroup R q) (@euclidean_power_regroup R q).
Proof.
move=> y; rewrite /euclidean_power_regroup /euclidean_power_ungroup euclidean_block_joinK.
exact (pair_power_shuffle_backwardK (@euclidean_pair_power_shuffle_specification R q) y).
Qed.

(** Source for [euclidean_power_regroup_distance]: direct
    metric isometry of the identification in
    2.10.29, p. 195. Squared-distance preservation
    is turned into distance equality using
    nonnegativity of the actual metric distances. *)
Lemma euclidean_power_regroup_distance (R : realType) q
    (x y : inner_metric_space (@euclidean_inner_productP R (q.+1+q.+1))) :
  mdist (@euclidean_power_regroup R q x) (@euclidean_power_regroup R q y)=mdist x y.
Proof.
have hh := pair_power_shuffle_squared_distance (@euclidean_pair_power_shuffle_specification R q)
  (@euclidean_block_split R q.+1 q.+1 x) (@euclidean_block_split R q.+1 q.+1 y).
rewrite -(@euclidean_block_squared_distance R q.+1 q.+1 x y) in hh.
change (mdist (@euclidean_power_regroup R q x) (@euclidean_power_regroup R q y)^+2=mdist x y^+2) in hh.
apply/eqP; rewrite eq_le; apply/andP; split;
  by rewrite -(ler_sqr _ _) ?nnegrE ?mdist_ge0 // hh.
Qed.

(** Source for [euclidean_power_ungroup_distance]: supporting
    inverse isometry in 2.10.29, p. 195,
    derived only from the forward metric
    law and the proved cancellation identity. *)
Lemma euclidean_power_ungroup_distance (R : realType) q
    (x y : inner_metric_space (@euclidean_inner_productP R (euclidean_power_dimension 2 q))) :
  mdist (@euclidean_power_ungroup R q x) (@euclidean_power_ungroup R q y)=mdist x y.
Proof.
have hh := @euclidean_power_regroup_distance R q (@euclidean_power_ungroup R q x) (@euclidean_power_ungroup R q y).
by rewrite !euclidean_power_ungroupK in hh; exact: esym hh.
Qed.

(** Source for [euclidean_power_regroup_image]: direct
    set image identity A^q*B^q to (A*B)^q
    in 2.10.29, p. 195, for arbitrary
    scalar sets A and B. *)
Theorem euclidean_power_regroup_image (R : realType) q (A B : set (real_line_metric R)) :
  (@euclidean_power_regroup R q) @` (@euclidean_power_product R q.+1 A B)=
    @euclidean_block_set_power R 2 (euclidean_cantor_product A B) q.
Proof.
have hmem x : @euclidean_block_set_power R 2 (euclidean_cantor_product A B) q (@euclidean_power_regroup R q x) <->
    @euclidean_power_product R q.+1 A B x.
  have hh := pair_power_shuffle_membership (@euclidean_pair_power_shuffle_specification R q) A B
    (@euclidean_block_split R q.+1 q.+1 x).1 (@euclidean_block_split R q.+1 q.+1 x).2.
  by rewrite -surjective_pairing in hh.
apply/seteqP; split.
- move=> y [x hx <-]; exact: (hmem x).2 hx.
- move=> y hy; exists (@euclidean_power_ungroup R q y); last exact: euclidean_power_ungroupK.
  apply: (hmem _).1; by rewrite euclidean_power_ungroupK.
Qed.
