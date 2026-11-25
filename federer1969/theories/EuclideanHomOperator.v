(** Federer (1969), 3.2.2, p. 242: finite-dimensional linear
    maps use the operator norm recalled from 1.7.6. This adapter
    identifies their whole Hom space with the abstract continuous
    operator space used for the Borel differential in 3.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP HomSpaceTopology
  ContinuousOperatorUP ContinuousOperatorNorm NormOperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_operator_norm]: the norm on the source
    automorphisms and differentials in the proof of Federer 3.2.2,
    p. 242. It is the existing abstract norm of 1.7.6. *)
Definition euclidean_operator_norm (R:realType) m n (L:Hom (R_n R m) (R_n R n)):R :=
  hom_operator_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    (@coordinate_basisP R m) L.

(** Source for [euclidean_hom_operator_space]: supporting finite
    operator-space parameterization for the Borel sets of Federer
    3.2.2, p. 242. Every linear map has the least homogeneous
    norm bound; evaluation is the identity on Hom, without a
    constructed coordinate replacement for the differential. *)
Theorem euclidean_hom_operator_space (R:realType) m n :
  is_continuous_operator_space (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n))
    (hom_of_linear (linear_id (Hom (R_n R m) (R_n R n))))
    (@euclidean_operator_norm R m n).
Proof.
constructor.
- by move=>x y.
- move=>L; exists (euclidean_operator_norm L); split.
  + exact:hom_operator_norm_nonnegative.
  + exact:hom_operator_norm_bound.
- by move=>L hL; exists L.
- move=>L; constructor.
  + exact:hom_operator_norm_nonnegative.
  + exact:hom_operator_norm_bound.
  + exact:hom_operator_norm_least.
Qed.

(** Source for [euclidean_operator_norm_is_norm]: the operator
    topology used for the countable dense family in Federer 3.2.2,
    p. 242. This is a norm by the abstract continuous-operator
    laws; its proof does not choose coordinates for Hom. *)
Lemma euclidean_operator_norm_is_norm (R:realType) m n :
  is_real_norm (@euclidean_operator_norm R m n).
Proof.
exact (@continuous_operator_norm_is_norm R (R_n R m) (R_n R n)
  (Hom (R_n R m) (R_n R n)) (inner_norm (@euclidean_inner_productP R m))
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n))
  (hom_of_linear (linear_id (Hom (R_n R m) (R_n R n))))
  (@euclidean_operator_norm R m n) (@euclidean_hom_operator_space R m n)).
Qed.
