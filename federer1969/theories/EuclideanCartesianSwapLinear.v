(** Federer (1969), 4.1.8, p. 361: the original
    coordinate interchange w(x,y)=(y,x) is the already
    defined Cartesian swap of 2.6.5, p. 120.
    These supporting laws reuse its coordinate blocks,
    inverse and the original bounded linear calculus. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormFiniteLinearBound NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinear
  EuclideanBlockLinearMaps EuclideanCartesianMap EuclideanCartesianSwap CurrentCartesianDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_cartesian_swap_linear]: the original
    interchange in Federer 4.1.8, p. 361 is linear,
    including empty coordinate blocks. *)
Lemma euclidean_cartesian_swap_linear (R:realType) m n:
  linear (@euclidean_cartesian_swap R m n).
Proof.
move=>c x y.
change (euclidean_block_join
  (@euclidean_last_block_map R m n (c*:x+y),@euclidean_first_block_map R m n (c*:x+y))=
  c*:euclidean_block_join (@euclidean_last_block_map R m n x,@euclidean_first_block_map R m n x)+
  euclidean_block_join (@euclidean_last_block_map R m n y,@euclidean_first_block_map R m n y)).
rewrite (hom_linear (@euclidean_last_block_map R m n) c x y)
  (hom_linear (@euclidean_first_block_map R m n) c x y).
exact:(@euclidean_block_join_linear R n m c
  (@euclidean_last_block_map R m n x,@euclidean_first_block_map R m n x)
  (@euclidean_last_block_map R m n y,@euclidean_first_block_map R m n y)).
Qed.

(** Source for [euclidean_cartesian_swap_map]: the existing
    original interchange as a linear map, supporting the
    pushforward identity in Federer 4.1.8, p. 361.
    This alias changes no coordinate values. *)
Definition euclidean_cartesian_swap_map (R:realType) m n:Hom (R_n R (m+n)) (R_n R (n+m)):=
  @HomMap R (R_n R (m+n)) (R_n R (n+m)) (@euclidean_cartesian_swap R m n)
    (introT (asboolP _) (@euclidean_cartesian_swap_linear R m n)).

(** Source for [euclidean_cartesian_swap_first]: the first
    block after the original interchange is the old
    second block, supporting Federer 4.1.8, p. 361. *)
Lemma euclidean_cartesian_swap_first (R:realType) m n (x:R_n R (m+n)):
  @euclidean_first_block_map R n m (@euclidean_cartesian_swap_map R m n x)=
    @euclidean_last_block_map R m n x.
Proof. exact:(congr1 fst (@euclidean_block_joinK R n m
  (@euclidean_last_block_map R m n x,@euclidean_first_block_map R m n x))). Qed.

(** Source for [euclidean_cartesian_swap_last]: the second
    block after the original interchange is the old
    first block, supporting Federer 4.1.8, p. 361. *)
Lemma euclidean_cartesian_swap_last (R:realType) m n (x:R_n R (m+n)):
  @euclidean_last_block_map R n m (@euclidean_cartesian_swap_map R m n x)=
    @euclidean_first_block_map R m n x.
Proof. exact:(congr1 snd (@euclidean_block_joinK R n m
  (@euclidean_last_block_map R m n x,@euclidean_first_block_map R m n x))). Qed.

Section SwapRegularity.
Variable R:realType.
Variables m n:nat.
Local Notation X := (R_n R (m+n)).
Local Notation Y := (R_n R (n+m)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation NY := (inner_norm (@euclidean_inner_productP R (n+m))).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R (n+m))).
Local Notation swap := (@euclidean_cartesian_swap_map R m n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.

(** Source for [euclidean_cartesian_swap_bounded]: boundedness
    of the original linear interchange follows from the
    existing finite-dimensional norm theorem, supporting Federer
    4.1.8, p. 361. *)
Lemma euclidean_cartesian_swap_bounded:norm_bounded_linear NX NY swap.
Proof. exact:(@norm_finite_linear_bounded R X Y NX NY hNX hNY (m+n)%N
  (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n)) swap). Qed.

(** Source for [euclidean_cartesian_swap_smooth]: the original
    interchange is smooth on every original open source,
    supporting the pushforward in Federer 4.1.8, p. 361. *)
Theorem euclidean_cartesian_swap_smooth:norm_class_all_orders hNX hNY U swap.
Proof. move=>k;exact:(@norm_class_linear R X Y NX NY hNX hNY U swap k hU
  euclidean_cartesian_swap_bounded). Qed.

(** Source for [euclidean_cartesian_swap_differential]: its
    actual differential is the same original linear swap,
    supporting the pulled-back separated tests in Federer
    4.1.8, p. 361. *)
Theorem euclidean_cartesian_swap_differential x:U x->
  has_norm_differential NX NY U swap x swap.
Proof.
move=>hx;apply:(@norm_differential_linear R X Y NX NY hNX hNY U x swap (@hU x hx)).
exact:euclidean_cartesian_swap_bounded.
Qed.
End SwapRegularity.
