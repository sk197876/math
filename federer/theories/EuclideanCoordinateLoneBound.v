(** Federer (1969), 4.1.3, p. 348: the coordinate-product
    kernel has small Euclidean support. This supporting norm
    estimate reuses the finite coordinate expansion and norm
    triangle inequality of 1.7.1, p. 28, including dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP GrassmannAbbreviations FiniteCoordinates
  FieldCoordinateExpansion EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanCoordinateMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_coordinate_lone_bound]: the finite
    coordinate norm bound supporting the product support in
    Federer 4.1.3, p. 348. *)
Lemma euclidean_coordinate_lone_bound (R:realType) n (x:R_n R n):
  inner_norm (@euclidean_inner_productP R n) x<=\sum_i `|x i|.
Proof.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
have h:=@real_seminorm_sum R (R_n R n) N hN.1 (Finite.clone 'I_n _)
  (fun i=>x i*:@coordinate_basis R n i).
rewrite field_coordinate_expansion in h.
apply:le_trans h _; apply:ler_sum=>i _.
change (N (x i*:@coordinate_basis R n i)<=`|x i|).
by rewrite /N inner_normZ euclidean_coordinate_unit_norm mulr1.
Qed.
