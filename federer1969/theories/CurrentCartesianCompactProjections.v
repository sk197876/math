(** Federer (1969), 4.1.8, p. 360: the two projections
    of a compact product-test support give compact bounds for
    the slice tests. This supporting existence statement uses
    the previously proved compact-image theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap SmoothCompactSet SmoothCompactImage
  CurrentCartesianDomain CurrentCartesianProjections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section CurrentCartesianCompactProjections.
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
Variable A:set X.
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).

(** Source for [current_cartesian_compact_projections]: the
    compact supports in A and B used by the defining
    slice in Federer 4.1.8, p. 360. Both bounds are
    exactly the original projection images, including empty factors. *)
Theorem current_cartesian_compact_projections (K:smooth_compact_set hNZ AB):
  exists KA:smooth_compact_set hNX A,exists KB:smooth_compact_set hNY B,
    smooth_compact_carrier KA=p @` smooth_compact_carrier K /\
    smooth_compact_carrier KB=q @` smooth_compact_carrier K.
Proof.
have hPA z (hz:AB z):A (p z):=
  ((@current_cartesian_domain_coordinates R m n A B z).1 hz).1.
have hQB z (hz:AB z):B (q z):=
  ((@current_cartesian_domain_coordinates R m n A B z).1 hz).2.
have hP:=@norm_class_continuous R Z X NZ NX hNZ hNX AB p 0%N
  (@current_cartesian_first_projection_smooth R m n A B hA hB 0%N).
have hQ:=@norm_class_continuous R Z Y NZ NY hNZ hNY AB q 0%N
  (@current_cartesian_last_projection_smooth R m n A B hA hB 0%N).
pose KA:=@smooth_compact_image R Z X NZ NX hNZ hNX AB A p hPA hP K.
pose KB:=@smooth_compact_image R Z Y NZ NY hNZ hNY AB B q hQB hQ K.
exists KA,KB;split;reflexivity.
Qed.
End CurrentCartesianCompactProjections.
