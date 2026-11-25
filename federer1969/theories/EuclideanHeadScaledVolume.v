(** Scalar-head scaling for the geometric connections in
    Federer (1969), 3.2.45, pp. 279–280.
    The existing determinant and Lebesgue image laws
    of 2.7.16(1), pp. 134–135, give the exact factor. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanLinearMaps EuclideanLebesgueDimensions EuclideanLebesgueDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_head_scaled_volume]: supporting
    target-coordinate scaling in the projection and
    pyramid arguments for Federer 3.2.45,
    pp. 279–280. The actual diagonal map
    multiplies the scalar head by a and fixes
    every tail coordinate. Its determinant is a,
    so the original outer volume is multiplied
    by the absolute value of a, by
    2.7.16(1), pp. 134–135. Arbitrary sets,
    a= 0 and an empty tail are retained
    with the established total determinant-product convention. *)
Theorem euclidean_head_scaled_volume (R : realType) n (a : R)
    (S : set (inner_metric_space (@euclidean_inner_productP R n.+1))) :
  euclidean_lebesgue_measure n.+1
    ((@euclidean_diagonal_map R n.+1 (fun i => if i==ord0 then a else 1)) @` S) =
    ((`|a|)%:E * euclidean_lebesgue_measure n.+1 S)%E.
Proof.
pose c := fun i : 'I_n.+1 => if i==ord0 then a else 1.
have hDet : euclidean_det (@euclidean_diagonal_map R n.+1 c)=a.
  rewrite euclidean_diagonal_det (bigD1 ord0) //.
  change ((if (ord0 : 'I_n.+1)==ord0 then a else 1) *
    (\prod_(i : 'I_n.+1 | i!=ord0) (if i==ord0 then a else 1))=a).
  have hOther : (\prod_(i : 'I_n.+1 | i!=ord0) (if i==ord0 then a else 1))= 1.
    apply: big1=> i hI; by rewrite (negbTE hI).
  by rewrite eqxx hOther mulr1.
rewrite euclidean_lebesgue_linear_image.
change ((`|euclidean_det (@euclidean_diagonal_map R n.+1 c)|)%:E*
  euclidean_lebesgue_measure n.+1 S = (`|a|)%:E*euclidean_lebesgue_measure n.+1 S)%E.
by rewrite hDet.
Qed.
