(** Federer (1969), 3.2.23, p. 260: interchange of Cartesian
    factors in the null-remainder argument. This is a proved isometry
    between the usual coordinate blocks, so 2.10.11 preserves every
    Hausdorff degree without introducing a replacement product metric. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanMetricProduct EuclideanCartesianMap
  HausdorffMeasure HausdorffIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_cartesian_swap]: supporting coordinate
    interchange (x,y) maps to (y,x) for Federer 3.2.23, p. 260. *)
Definition euclidean_cartesian_swap (R:realType) n v (p:R_n R (n+v)):R_n R (v+n):=
  euclidean_block_join ((euclidean_block_split p).2,(euclidean_block_split p).1).

(** Source for [euclidean_cartesian_swapK]: supporting inverse
    law for the factor interchange in Federer 3.2.23, p. 260. *)
Lemma euclidean_cartesian_swapK (R:realType) n v:
  cancel (@euclidean_cartesian_swap R n v) (@euclidean_cartesian_swap R v n).
Proof.
move=>p; rewrite /euclidean_cartesian_swap euclidean_block_joinK /=.
exact:euclidean_block_splitK.
Qed.

(** Source for [euclidean_cartesian_swap_distance]: orthogonal
    factor interchange preserves distance, supporting the product
    null-remainder calculation in Federer 3.2.23, p. 260. *)
Lemma euclidean_cartesian_swap_distance (R:realType) n v
    (p q:inner_metric_space (@euclidean_inner_productP R (n+v))):
  mdist (euclidean_cartesian_swap p:inner_metric_space (@euclidean_inner_productP R (v+n))) (euclidean_cartesian_swap q)=mdist p q.
Proof.
have hSquare:mdist (euclidean_cartesian_swap p:inner_metric_space (@euclidean_inner_productP R (v+n))) (euclidean_cartesian_swap q)^+2=mdist p q^+2.
  by rewrite !euclidean_block_squared_distance /euclidean_cartesian_swap !euclidean_block_joinK /= addrC.
apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite -ler_sqr ?nnegrE ?mdist_ge0 // hSquare; exact:lexx.
- rewrite -ler_sqr ?nnegrE ?mdist_ge0 // hSquare; exact:lexx.
Qed.

(** Source for [euclidean_cartesian_swap_set]: the exact set
    identity for factor interchange, supporting Federer 3.2.23, p. 260.
    It includes empty and nonmeasurable factors. *)
Lemma euclidean_cartesian_swap_set (R:realType) n v
    (W:set (R_n R n)) (Z:set (R_n R v)):
  (@euclidean_cartesian_swap R n v) @` euclidean_cartesian_set W Z=euclidean_cartesian_set Z W.
Proof.
apply/seteqP; split.
- move=>p [q [hqW hqZ] <-].
  change (Z (euclidean_block_split (euclidean_cartesian_swap q)).1 /\
    W (euclidean_block_split (euclidean_cartesian_swap q)).2).
  by rewrite /euclidean_cartesian_swap euclidean_block_joinK; split.
- move=>p [hpZ hpW]; exists (euclidean_cartesian_swap p).
  + change (W (euclidean_block_split (euclidean_cartesian_swap p)).1 /\
      Z (euclidean_block_split (euclidean_cartesian_swap p)).2).
    by rewrite /euclidean_cartesian_swap euclidean_block_joinK; split.
  + exact:euclidean_cartesian_swapK.
Qed.

(** Source for [euclidean_cartesian_swap_hausdorff]: Hausdorff
    measure is unchanged by interchanging the two factors, supporting
    both null remainders in Federer 3.2.23, p. 260. The degree
    is arbitrary and need not be bounded by either ambient dimension. *)
Lemma euclidean_cartesian_swap_hausdorff (R:realType) n v k
    (W:set (R_n R n)) (Z:set (R_n R v)):
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+v))) k
    (euclidean_cartesian_set W Z)=
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (v+n))) k
    (euclidean_cartesian_set Z W).
Proof.
have h:=@hausdorff_bijective_isometry_invariance R
  (inner_metric_space (@euclidean_inner_productP R (n+v)))
  (inner_metric_space (@euclidean_inner_productP R (v+n)))
  (@euclidean_cartesian_swap R n v) (@euclidean_cartesian_swap R v n)
  (@euclidean_cartesian_swapK R n v) (@euclidean_cartesian_swapK R v n)
  (@euclidean_cartesian_swap_distance R n v) k (euclidean_cartesian_set W Z).
rewrite (@euclidean_cartesian_swap_set R n v W Z) in h.
exact:esym h.
Qed.
