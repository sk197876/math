(** Federer (1969), 4.1.11, p. 366: the
    canonical block regroupings used in the original
    associativity argument are smooth. Reuse the proved
    finite-dimensional linear and affine calculus. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom AffineMaps RealNormUP NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanAffineSmooth
  CurrentJoinAssociativityRegroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinAssociativityRegroupClass.
Variable R:realType.
Variable n:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).

(** Source for [current_join_assoc_inner_association_smooth]: smoothness of the
    original inner association identification, supporting
    Federer 4.1.11, p. 366, including empty spatial blocks. *)
Lemma current_join_assoc_inner_association_smooth:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R (n+(2+n))%N))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+(1+n)))%N))
    (Full (n+(2+n))%N) (@current_join_assoc_inner_association R n).
Proof.
exact:(@euclidean_affine_map_smooth R (n+(2+n))%N (n+(1+(1+n)))%N (Full (n+(2+n))%N) (hFull (n+(2+n))%N)
  (@current_join_assoc_inner_association R n)
  (@linear_affine_map R (R_n R (n+(2+n))%N) (R_n R (n+(1+(1+n)))%N)
    (hom_as_linear (@current_join_assoc_inner_association R n)))).
Qed.

(** Source for [current_join_assoc_inner_regroup_smooth]: smoothness of the
    original inner regroup identification, supporting
    Federer 4.1.11, p. 366, including empty spatial blocks. *)
Lemma current_join_assoc_inner_regroup_smooth:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R (n+(2+n))%N))
    (inner_norm_real_norm (@euclidean_inner_productP R (1+(n+(1+n)))%N))
    (Full (n+(2+n))%N) (@current_join_assoc_inner_regroup R n).
Proof.
exact:(@euclidean_affine_map_smooth R (n+(2+n))%N (1+(n+(1+n)))%N (Full (n+(2+n))%N) (hFull (n+(2+n))%N)
  (@current_join_assoc_inner_regroup R n)
  (@linear_affine_map R (R_n R (n+(2+n))%N) (R_n R (1+(n+(1+n)))%N)
    (hom_as_linear (@current_join_assoc_inner_regroup R n)))).
Qed.

(** Source for [current_join_assoc_common_regroup_smooth]: smoothness of the
    original common regroup identification, supporting
    Federer 4.1.11, p. 366, including empty spatial blocks. *)
Lemma current_join_assoc_common_regroup_smooth:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R (n+(n+(2+n)))%N))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+(n+(1+n))))%N))
    (Full (n+(n+(2+n)))%N) (@current_join_assoc_common_regroup R n).
Proof.
exact:(@euclidean_affine_map_smooth R (n+(n+(2+n)))%N (n+(1+(n+(1+n))))%N (Full (n+(n+(2+n)))%N) (hFull (n+(n+(2+n)))%N)
  (@current_join_assoc_common_regroup R n)
  (@linear_affine_map R (R_n R (n+(n+(2+n)))%N) (R_n R (n+(1+(n+(1+n))))%N)
    (hom_as_linear (@current_join_assoc_common_regroup R n)))).
Qed.

(** Source for [current_join_assoc_weight_regroup_smooth]: smoothness of the
    original weight regroup identification, supporting
    Federer 4.1.11, p. 366, including empty spatial blocks. *)
Lemma current_join_assoc_weight_regroup_smooth:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R (n+(n+(3+n)))%N))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+(n+(n+3)))%N))
    (Full (n+(n+(3+n)))%N) (@current_join_assoc_weight_regroup R n).
Proof.
exact:(@euclidean_affine_map_smooth R (n+(n+(3+n)))%N (n+(n+(n+3)))%N (Full (n+(n+(3+n)))%N) (hFull (n+(n+(3+n)))%N)
  (@current_join_assoc_weight_regroup R n)
  (@linear_affine_map R (R_n R (n+(n+(3+n)))%N) (R_n R (n+(n+(n+3)))%N)
    (hom_as_linear (@current_join_assoc_weight_regroup R n)))).
Qed.
End CurrentJoinAssociativityRegroupClass.
