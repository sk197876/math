(** Federer (1969), 3.1.19(4), p. 231, as used
    by the coordinate criteria in 3.1.22, pp. 235–236. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDifferentialUP NormClassOneUP NormRegularity EuclideanSubmanifoldUP
  SubmanifoldChartsUP SubmanifoldStraighteningCoordinates NormCoordinateSystemUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [submanifold_coordinate_system_exists]: existence
    of a coordinate system at each point, Federer 3.1.19,
    p. 231, supporting the some/every assertions of
    3.1.22, pp. 235–236. The original convex parameter
    neighbourhood is retained by the existence proof. *)
Theorem submanifold_coordinate_system_exists (R:realType) n mu k (B:set (R_n R n)) :
  @is_euclidean_submanifold R n mu k B ->
  forall a,B a -> exists T V phi psi,
    T a /\ is_norm_coordinate_system
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R mu)) B T V phi psi k.
Proof.
move=>hB a ha.
have [T [V [phi [psi [hTa [hconv [hphi [hpsi [hmap [hback [him hcan]]]]]]]]]]]:=
  submanifold_convex_coordinates hB ha.
exists T,V,phi,psi; split.
- exact (norm_domain_interior_member (inner_norm_real_norm (@euclidean_inner_productP R n)) hTa).
- by constructor.
Qed.

(** Source for [submanifold_differentiable_coordinates_exist]: the
    actual derivatives of phi and psi used in Federer
    3.1.22, p. 236. Their existence follows from
    the proved class-one coordinate system, including mu=0. *)
Theorem submanifold_differentiable_coordinates_exist (R:realType) n mu (B:set (R_n R n)) :
  @is_euclidean_submanifold R n mu 1 B ->
  forall a,B a -> exists T V phi psi (E:Hom (R_n R n) (R_n R mu)) (J:Hom (R_n R mu) (R_n R n)),
    T a /\ is_norm_coordinate_system
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R mu)) B T V phi psi 1 /\
    has_norm_differential (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R mu)) T phi a E /\
    has_norm_differential (inner_norm (@euclidean_inner_productP R mu))
      (inner_norm (@euclidean_inner_productP R n)) V psi (phi a) J.
Proof.
move=>hB a ha; have [T [V [phi [psi [ht hc]]]]]:=submanifold_coordinate_system_exists hB ha.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNZ:=inner_norm_real_norm (@euclidean_inner_productP R mu).
have [E hE]:=(norm_class_firstP hNX hNZ T phi).1 (norm_coordinate_class_forward hc).
have [J hJ]:=(norm_class_firstP hNZ hNX V psi).1 (norm_coordinate_class_backward hc).
exists T,V,phi,psi,(E a),(J (phi a)); split=>//; split=>//; split.
- exact (norm_class_one_differential hE ht).
- exact (norm_class_one_differential hJ (norm_coordinate_forward_range hc ht)).
Qed.
