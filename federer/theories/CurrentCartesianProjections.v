(** Federer (1969), 4.1.8, p. 360: the Cartesian projections
    p and q are smooth and have their original constant differentials.
    All maps are the existing block projections of 2.6.5, p. 120.
    The earlier finite-dimensional linear bound and linear calculus
    prove these supporting laws, including empty coordinate blocks. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormFiniteLinearBound NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  CurrentCartesianDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianProjections.
Variable R:realType.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Variable A:set X.
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).

(** Source for [current_cartesian_first_projection_smooth]: the
    original first projection used in p#alpha in Federer 4.1.8,
    p. 360 is of every finite class. This supporting consequence
    uses the linear calculus of 3.1.11, pp. 220–221. *)
Theorem current_cartesian_first_projection_smooth:
  norm_class_all_orders hNZ hNX AB p.
Proof.
move=>k.
apply:(@norm_class_linear R Z X NZ NX hNZ hNX AB p k hAB).
exact:(@norm_finite_linear_bounded R Z X NZ NX hNZ hNX (m+n)%N
  (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n)) p).
Qed.

(** Source for [current_cartesian_last_projection_smooth]: the
    original second projection used in q#beta in Federer 4.1.8,
    p. 360 is of every finite class, with the same original
    Cartesian source and no restriction on either block dimension. *)
Theorem current_cartesian_last_projection_smooth:
  norm_class_all_orders hNZ hNY AB q.
Proof.
move=>k.
apply:(@norm_class_linear R Z Y NZ NY hNZ hNY AB q k hAB).
exact:(@norm_finite_linear_bounded R Z Y NZ NY hNZ hNY (m+n)%N
  (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n)) q).
Qed.

(** Source for [current_cartesian_first_projection_differential]:
    Dp is the original first block projection in Federer 4.1.8,
    p. 360, in the paragraph verifying the product condition.
    The differential is computed on A times B itself. *)
Theorem current_cartesian_first_projection_differential z:AB z->
  has_norm_differential NZ NX AB p z p.
Proof.
move=>hz.
apply:(@norm_differential_linear R Z X NZ NX hNZ hNX AB z p (@hAB z hz)).
exact:(@norm_finite_linear_bounded R Z X NZ NX hNZ hNX (m+n)%N
  (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n)) p).
Qed.

(** Source for [current_cartesian_last_projection_differential]:
    Dq is the original second block projection in Federer 4.1.8,
    p. 360, in the same verification. Empty factor domains and
    empty blocks retain the earlier differential convention. *)
Theorem current_cartesian_last_projection_differential z:AB z->
  has_norm_differential NZ NY AB q z q.
Proof.
move=>hz.
apply:(@norm_differential_linear R Z Y NZ NY hNZ hNY AB z q (@hAB z hz)).
exact:(@norm_finite_linear_bounded R Z Y NZ NY hNZ hNY (m+n)%N
  (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n)) q).
Qed.
End CurrentCartesianProjections.
