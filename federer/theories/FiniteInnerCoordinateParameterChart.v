(** Federer (1969), 3.2.48, p. 285: use orthonormal Euclidean
    coordinates on the product parameter space. Supporting the original
    submanifold criterion of 3.1.19(4), p. 231. Both coordinate maps
    and their inverse domain are used through actual chart laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness FiniteInnerChartUP
  NormDifferentialUP NormRegularityLinearMaps NormCoordinateSystemUP InnerConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_coordinate_parameter_chart]: the actual
    Euclidean parameter coordinates of the Cartesian source manifold in
    3.2.48, p. 285. The inverse-image parameter domain is exact;
    no ambient or manifold dimension is changed by the chart. *)
Theorem finite_inner_coordinate_parameter_chart (R:realType) (X Z:lmodType R)
    BX BZ (hX:@is_inner_product R X BX) (hZ:@is_inner_product R Z BZ)
    n (e:Hom (R_n R n) Z) (p:Hom Z (R_n R n))
    (M T:set X) (U:set Z) (phi:X->Z) (psi:Z->X) k:
  is_finite_inner_chart BZ e p ->
  is_norm_coordinate_system (inner_norm_real_norm hX) (inner_norm_real_norm hZ) M T U phi psi k ->
  is_norm_coordinate_system (inner_norm_real_norm hX)
    (inner_norm_real_norm (@euclidean_inner_productP R n)) M T (fun u=>U (e u))
    (fun x=>p (phi x)) (fun u=>psi (e u)) k.
Proof.
move=>hChart hC.
have he:norm_bounded_linear (inner_norm (@euclidean_inner_productP R n)) (inner_norm hZ) e.
  exists 1; split; first exact:ler01.
  by move=>u; rewrite (finite_inner_chart_norm hZ hChart) mul1r.
have hp:norm_bounded_linear (inner_norm hZ) (inner_norm (@euclidean_inner_productP R n)) p.
  exists 1; split; first exact:ler01.
  by move=>u; rewrite (finite_inner_chart_inverse_norm hZ hChart) mul1r.
constructor.
- exact (@norm_class_postcompose_linear R X Z (R_n R n) _ _ _ (inner_norm_real_norm hX)
    (inner_norm_real_norm hZ) (inner_norm_real_norm (@euclidean_inner_productP R n)) T phi p k hp
    (norm_coordinate_class_forward hC)).
- exact (@norm_class_precompose_linear R (R_n R n) Z X _ _ _ (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm hZ) (inner_norm_real_norm hX) U psi e k he (norm_coordinate_class_backward hC)).
- move=>x hx; rewrite (finite_inner_chart_right_inverse hChart).
  exact (norm_coordinate_forward_range hC hx).
- apply/seteqP; split=>x.
  + move=>[u hu <-]; exact (norm_coordinate_backward_membership hC hu).
  + move=>hx; have hImage:(psi @` U) x by rewrite (norm_coordinate_image hC).
    have [u hu hux]:=hImage.
    exists (p u).
    * by rewrite (finite_inner_chart_right_inverse hChart).
    * by rewrite (finite_inner_chart_right_inverse hChart).
- move=>u hu.
  rewrite (norm_coordinate_cancel hC hu).
  exact (finite_inner_chart_left_inverse hChart u).
Qed.

(** Source for [inner_convex_linear_inverse_image]: the exact convex
    Euclidean parameter domain for the source Cartesian charts of
    3.2.48, p. 285. This is the convexity definition in 1.7.13,
    p. 37, applied to a linear inverse image. *)
Lemma inner_convex_linear_inverse_image (R:realType) (V W:lmodType R)
    (U:set W) (L:Hom V W):
  is_inner_convex U ->is_inner_convex (fun x=>U (L x)).
Proof.
move=>hU x y hx hy t ht ht1.
rewrite linearD !linearZ; exact (hU (L x) (L y) hx hy t ht ht1).
Qed.
