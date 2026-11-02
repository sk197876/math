(** Federer (1969), 3.2.9, p. 247: complete
    countable Borel coordinate cover theorem for a
    continuous map R^m to R^n. The printed
    full-rank locus, orthogonal projection and global
    forward/inverse Lipschitz laws are all retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness NormMetric
  NormClassOneUP NormClassZeroWhole CoordinateInverseCoverUP CoordinateInverseCoverExistence
  SurjectiveDifferentialDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_inverse_cover_class_zero]:
    intrinsic continuity form of Federer 3.2.9,
    p. 247. Introduce a complementary dimension
    when n<=m and use the empty cover
    otherwise. No dimensional hypothesis is imposed. *)
Theorem coordinate_inverse_cover_class_zero (R:realType) m n
    (f:R_n R m->R_n R n):
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  exists G,is_coordinate_inverse_cover f G.
Proof.
move=>hf; case:(leqP n m)=>hnm.
- have [k he]:exists k:nat,m=(n+k)%N.
    exists (m-n)%N; by rewrite subnKC.
  subst m; exact:coordinate_inverse_cover_complementary_dimensions hf.
- exists set0; split; first exact:countable0.
  split; last by move=>E [].
  rewrite (surjective_differential_locus_above_dimension_empty f hnm).
  by move=>x [].
Qed.

(** Source for [federer_3_2_9]: the complete
    lemma of Federer 3.2.9, p. 247.
    Continuity is the only hypothesis. Each
    Borel piece has its projection in O*(m,m-n)
    and two global Lipschitz maps with the
    exact printed coordinate and left-inverse laws. *)
Theorem federer_3_2_9 (R:realType) m n
    (f:R_n R m->R_n R n):
  continuous (fun x:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m))=>
    (f x:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))) ->
  exists G,is_coordinate_inverse_cover f G.
Proof.
move=>hf; apply:coordinate_inverse_cover_class_zero.
exact (@norm_continuous_whole_class_zero R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) f hf).
Qed.
