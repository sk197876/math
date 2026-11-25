(** Federer (1969), 3.4.4, p. 318: actual
    scalar and one-dimensional coordinate maps for the product example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP EuclideanOneCoordinate NormDifferentialUP
  NormFiniteLinearBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_scalar_coordinate_map]: the
    coordinate x_i used in 3.4.4, p. 318,
    as its actual linear functional. *)
Definition euclidean_scalar_coordinate_map (R:realType) m (i:'I_m):Hom (R_n R m) R^o.
Proof.
apply:(@HomMap R (R_n R m) R^o (fun x=>x i)).
apply/asboolP=>c x y;by rewrite !ffunE.
Defined.
Arguments euclidean_scalar_coordinate_map {R m} i.

(** Source for [euclidean_one_coordinate_map]: the same
    printed coordinate identified with the canonical line R^1,
    3.4.4, p. 318. *)
Definition euclidean_one_coordinate_map (R:realType) m (i:'I_m):Hom (R_n R m) (R_n R 1).
Proof.
apply:(@HomMap R (R_n R m) (R_n R 1) (fun x=>euclidean_one_embed (x i))).
apply/asboolP=>c x y;apply/ffunP=>j.
by rewrite /euclidean_one_embed !ffunE.
Defined.
Arguments euclidean_one_coordinate_map {R m} i.

(** Source for [euclidean_scalar_coordinate_bounded]: boundedness
    of the printed source coordinates, supporting class k
    of the map in 3.4.4, p. 318. *)
Lemma euclidean_scalar_coordinate_bounded (R:realType) m (i:'I_m):
  norm_bounded_linear (inner_norm (@euclidean_inner_productP R m))
    (fun t:R^o=>`|t|) (euclidean_scalar_coordinate_map i).
Proof.
exact:(@norm_finite_linear_bounded R (R_n R m) R^o _ _
  (inner_norm_real_norm (@euclidean_inner_productP R m)) (@scalar_absolute_value_norm R)
  m (@coordinate_basis R m) (@coordinate_basisP R m) (euclidean_scalar_coordinate_map i)).
Qed.
Arguments euclidean_scalar_coordinate_bounded {R m} i.

(** Source for [euclidean_one_coordinate_bounded]: boundedness
    of the canonical one-dimensional coordinate used in the
    Whitney product map, 3.4.4, p. 318. *)
Lemma euclidean_one_coordinate_bounded (R:realType) m (i:'I_m):
  norm_bounded_linear (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R 1)) (euclidean_one_coordinate_map i).
Proof.
exact:(@norm_finite_linear_bounded R (R_n R m) (R_n R 1) _ _
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R 1))
  m (@coordinate_basis R m) (@coordinate_basisP R m) (euclidean_one_coordinate_map i)).
Qed.

Arguments euclidean_one_coordinate_bounded {R m} i.
