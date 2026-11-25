(** Federer (1969), 4.1.11, p. 365: the original
    point product is a compact point-inclusion image.
    This adapter reuses the complete point-product law
    of 4.1.8, p. 362, with the compact properness witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap CurrentSpaces CurrentDirac CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianPointInclusion CurrentCartesianPointInclusionProper CurrentCartesianPointProduct
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra CurrentPushforwardCongruence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCompactPointProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n j:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A x.
Hypothesis hB:forall y,B y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B y.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Variable a:R_n R m.
Hypothesis ha:A a.
Variable T:@current_space R h2 n B hB j.
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n B hB j T).
Local Notation inclusion := (@current_cartesian_point_inclusion R m n a).
Local Notation Image := (fun y hy=>@current_cartesian_point_inclusion_image R m n A B a ha y hy).
Local Notation Smooth := (@current_cartesian_point_inclusion_smooth R m n B hB a).

(** Source for [current_compact_point_product]: delta_a times T
    is the actual compact point-inclusion pushforward of T,
    supporting the cone and simplex identities in Federer
    4.1.11, p. 365. No representation hypothesis is imposed. *)
Theorem current_compact_point_product:
  @CartesianCurrentProduct.value R h2 m n 0%N j A B hA hB (@dirac_current R h2 m A hA a) T=
  @current_compact_map_pushforward R h2 n (m+n)%N B AB hB hAB inclusion Image Smooth j T hT.
Proof.
rewrite current_cartesian_point_product /current_cartesian_point_pushforward.
exact:(@current_pushforward_current_congruence R h2 n (m+n)%N j B AB hB hAB
  inclusion Image Smooth T T
  (@current_cartesian_point_inclusion_proper R h2 m n j A B hA hB a ha T)
  (@current_compact_map_proper R h2 n (m+n)%N j B AB hB T inclusion Image
    (norm_class_continuous (Smooth 0%N)) hT) (erefl T)).
Qed.
End CurrentCompactPointProduct.
