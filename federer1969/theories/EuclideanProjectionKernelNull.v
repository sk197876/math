(** Supporting the exceptional-projection argument in Federer (1969),
    2.10.46, p. 204, referred to Freilich (1950), Lemma 4.4, p. 240. Every
    orthogonal projection to a positive-dimensional space has a
    Lebesgue-null kernel. This auxiliary assertion follows from the
    hyperplane nullity used in Federer's 2.7.16(1), pp. 134–135. It supports
    a Fubini proof of the exceptional-set assertion; it does not itself
    assert nullity in projection probability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  InnerProductUP EuclideanNormalChart OrthogonalMaps OrthonormalFamilies CoordinateProjection
  AdjointUP Bilinear TensorUP EuclideanLebesgueDimensions EuclideanLebesgueDeterminant MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_unit_normal_hyperplane_null]: supporting
    arbitrary unit-normal version of the hyperplane nullity in
    2.7.16(1), pp. 134–135, used for 2.10.46,
    p. 204. The sealed normal chart supplies an
    orthonormal basis containing the given normal. *)
Lemma euclidean_unit_normal_hyperplane_null (R : realType) n (j : 'I_n)
    (u : R_n R n) (hu : euclidean_inner_product u u= 1) :
  euclidean_lebesgue_measure n [set x : inner_metric_space (@euclidean_inner_productP R n) |
    euclidean_inner_product x u=0]=0%:E.
Proof.
pose c := euclidean_normal_chart_forward j hu.
have he : orthonormal_family (@euclidean_inner_product R n) (@coordinate_basis R n).
  by move=> i l; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
have hc := orthogonal_map_orthonormal (euclidean_normal_chart_orthogonal j hu) he.
have hz := @euclidean_hyperplane_null R n (fun i=>c (@coordinate_basis R n i)) j hc.
by rewrite /c euclidean_normal_chart_axis in hz.
Qed.

(** Source for [euclidean_positive_projection_kernel_null]: supporting
    fixed-projection kernel nullity for 2.10.46, p. 204,
    and Freilich (1950), Lemma 4.4, p. 240.
    The kernel lies in the hyperplane perpendicular to the
    adjoint image of the first target basis vector. Positive
    dimensions are explicit; no assertion is made for the map
    to the zero-dimensional space, whose kernel is the whole source. *)
Theorem euclidean_positive_projection_kernel_null (R : realType) n m
    (p : {linear R_n R n.+1 -> R_n R m.+1}) :
  O_star p -> euclidean_lebesgue_measure n.+1
    [set x : inner_metric_space (@euclidean_inner_productP R n.+1) | p x=0]=0%:E.
Proof.
move=> [a [ha hap]].
pose u := a (@coordinate_basis R m.+1 ord0).
have hu : euclidean_inner_product u u= 1.
  rewrite /u ha euclidean_inner_basis /coordinate_basis ffunE eqxx; by [].
have hn := @euclidean_unit_normal_hyperplane_null R n.+1 ord0 u hu.
apply/eqP; rewrite eq_le; apply/andP; split; last exact: measure_nonnegative (euclidean_lebesgue_is_measure R n.+1) _.
rewrite -hn; apply: (measure_mono (euclidean_lebesgue_is_measure R n.+1))=> x hx.
change (euclidean_inner_product x (a (@coordinate_basis R m.+1 ord0))=0).
rewrite (inner_symmetric (@euclidean_inner_productP R n.+1)) -hap hx.
by rewrite (bil0r (inner_bilinear (@euclidean_inner_productP R m.+1))).
Qed.
