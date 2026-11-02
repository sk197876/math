(** Federer (1969), 3.2.28(3), pp. 265–266:
    the factor 2^(-1/2) normalizes each skew
    tangent direction and occurs in the differential
    of the forgetful map. Its scalar laws are proved here. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct OrthogonalMaps
  OrthonormalFamilies EuclideanHomInnerCharts EuclideanSkewIndexCardinality
  EuclideanStiefelAdaptedDirections EuclideanStiefelAdaptedOrthonormal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_stiefel_half_normalization]:
    2^(-1/2)>0 and twice its square is one,
    supporting the a_ij normalization in Federer
    3.2.28(3), p. 265. *)
Lemma euclidean_stiefel_half_normalization (R:realType):
  0<(Num.sqrt (2:R))^-1 /\
  2*(Num.sqrt (2:R))^-1*(Num.sqrt (2:R))^-1= 1.
Proof.
have hPos:0<Num.sqrt (2:R) by rewrite sqrtr_gt0 ltr0n.
split; first by rewrite invr_gt0.
have hTwo:0<(2:R) by rewrite ltr0n.
have hSq:Num.sqrt (2:R)^+2= 2:=sqr_sqrtr (ltW hTwo).
by rewrite -mulrA -expr2 exprVn hSq mulfV ?pnatr_eq0.
Qed.

(** Source for [euclidean_stiefel_normalized_skew_family]:
    the exactly normalized orthonormal family printed in
    Federer 3.2.28(3), p. 265, for every
    actual orthonormal source frame and target injection. *)
Theorem euclidean_stiefel_normalized_skew_family (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)) (e:'I_m->R_n R m):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (hom_as_linear g) ->orthonormal_family (@euclidean_inner_product R m) e ->
  orthonormal_family (@euclidean_hom_inner_product R m n)
    (fun p:euclidean_skew_indices m=>euclidean_stiefel_skew_direction g e
      (Num.sqrt (2:R))^-1 (val p).1 (val p).2).
Proof.
move=>hG hE; exact:(@euclidean_stiefel_skew_family_orthonormal R m n g e
  (Num.sqrt (2:R))^-1 hG hE (euclidean_stiefel_half_normalization R).2).
Qed.
