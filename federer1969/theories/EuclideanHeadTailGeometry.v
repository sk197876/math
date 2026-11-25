(** Federer (1969), 2.10.29, p. 195: orthogonal regrouping of the scalar
    coordinates in the two Cartesian powers. The supporting squared distance
    identity separates a scalar head and its Euclidean tail using the
    existing dot product. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  InnerNorm InnerNormedTopology EuclideanCoordinateSplit EuclideanSetPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

(** Source for [euclidean_head_tail_squared_distance]: supporting
    Pythagorean coordinate split for the orthogonal
    regrouping in 2.10.29, p. 195. Empty
    tail dimension is included. *)
Lemma euclidean_head_tail_squared_distance (R : realType) n
    (x y : inner_metric_space (@euclidean_inner_productP R n.+1)) :
  mdist x y^+2=
    mdist (@coordinate_tail R n x : inner_metric_space (@euclidean_inner_productP R n)) (@coordinate_tail R n y)^+2+
    `|coordinate_head x-coordinate_head y|^+2.
Proof.
rewrite !inner_metric_normE !inner_norm_topologyE !inner_norm_sqr
  /euclidean_inner_product big_ord_recl /coordinate_head /coordinate_tail !ffunE
  real_normK ?num_real // expr2.
have hsum : (\sum_(i : 'I_n) (y-x) (lift ord0 i)*(y-x) (lift ord0 i))=
    \sum_(i : 'I_n) (@coordinate_tail R n y-@coordinate_tail R n x) i*
      (@coordinate_tail R n y-@coordinate_tail R n x) i.
  apply: eq_bigr=> i _; by rewrite /coordinate_tail !ffunE.
rewrite hsum [LHS]addrC; congr (_+_); ring.
Qed.
