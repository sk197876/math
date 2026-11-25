(** Federer (1969), 4.1.20, p. 378: the orthogonal and
    coordinate maps in the proof are smooth, with their
    actual linear maps as differentials. Reuse the finite
    Euclidean operator-space laws of 1.7.6, pp. 33–34, and
    the original bounded-linear calculus of 3.1.1(3), p. 210,
    and 3.1.11, pp. 220–221. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormRegularity NormRegularityOperations InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ContinuousOperatorUP EuclideanHomOperator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section LinearData.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variable L:Hom X Y.

(** Source for [current_euclidean_linear_bounded]: the original
    maps in Federer 4.1.20, p. 378, have finite homogeneous
    bounds by the earlier finite operator norm, 1.7.6, pp. 33–34. *)
Lemma current_euclidean_linear_bounded:norm_bounded_linear NX NY L.
Proof.
have h:=continuous_operator_bounded (@euclidean_hom_operator_space R n nu) L.
exact:h.
Qed.

Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.

(** Source for [current_euclidean_linear_smooth]: the original
    orthogonal and coordinate maps are smooth on each open U,
    implicit in Federer 4.1.20, p. 378, by 3.1.11, pp. 220–221. *)
Theorem current_euclidean_linear_smooth:
  norm_class_all_orders hNX hNY U L.
Proof.
move=>k;exact:(@norm_class_linear R X Y NX NY hNX hNY U L k hU
  current_euclidean_linear_bounded).
Qed.

(** Source for [current_euclidean_linear_differential]: the actual
    original Dg=g and Dp_lambda=p_lambda used in Federer
    4.1.20, p. 378, follow from 3.1.1(3), p. 210. *)
Theorem current_euclidean_linear_differential x:U x->
  has_norm_differential NX NY U L x L.
Proof.
move=>hx;exact:(@norm_differential_linear R X Y NX NY hNX hNY U x L
  (@hU x hx) current_euclidean_linear_bounded).
Qed.
End LinearData.
