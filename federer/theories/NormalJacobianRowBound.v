(** Supporting Federer (1969), 3.2.45, p. 279: the
    earlier exterior Hadamard bound controls the volume of a linear
    image when one scalar row is small. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps InnerNorm
  Adjoint ExteriorGrading FiniteExteriorPowers ExteriorMaps ExteriorOperatorEstimate ExteriorNorm ExteriorHadamardBound
  EuclideanNormalJacobian ExteriorFrameUnitNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normal_jacobian_row_product_bound]: expanded
    support for Federer 3.2.45, p. 279, by the product-norm
    inequality of 1.7.5, p. 32. The actual adjoint rows give
    the normal Jacobian of 2.10.16, p. 178. The empty row
    family and every singular map are included. *)
Lemma normal_jacobian_row_product_bound (R : realType) n m
    (F : {linear R_n R n -> R_n R m}) (c : 'I_m -> R) :
  (forall i, inner_norm (@euclidean_inner_productP R n)
    (inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
      (@coordinate_basisP R n) F (@coordinate_basis R m i)) <= c i) ->
  euclidean_normal_jacobian F <= \prod_i c i.
Proof.
move=> hRows.
pose A := inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
  (@coordinate_basisP R n) F.
rewrite (@euclidean_normal_jacobian_unit_value R n m F
  (e_lambda (@coordinate_basis R m) (ord_tuple m))
  (euclidean_top_product_unit_norm (euclidean_two_nonzero R) m)).
rewrite exterior_map_indexed_product.
apply: le_trans (@exterior_product_norm_bound R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m
  (fun i => A (@coordinate_basis R m i))) _.
apply: ler_prod=> i _; apply/andP; split; first exact: inner_norm_nonnegative.
exact: hRows.
Qed.

(** Source for [normal_jacobian_one_small_row]: expanded
    continuity helper for Federer 3.2.45, p. 279. If one
    actual row has norm at most delta and every other row has norm
    at most one, the normal Jacobian is at most delta. A supplied
    row index already entails positive target dimension. *)
Lemma normal_jacobian_one_small_row (R : realType) n m
    (F : {linear R_n R n -> R_n R m}) (i0 : 'I_m) (delta : R) :
  inner_norm (@euclidean_inner_productP R n)
    (inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
      (@coordinate_basisP R n) F (@coordinate_basis R m i0)) <= delta ->
  (forall i, i != i0 -> inner_norm (@euclidean_inner_productP R n)
    (inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
      (@coordinate_basisP R n) F (@coordinate_basis R m i)) <= 1) ->
  euclidean_normal_jacobian F <= delta.
Proof.
move=> hSmall hOther.
pose c (i : 'I_m) : R := if i == i0 then delta else 1.
have hRows i : inner_norm (@euclidean_inner_productP R n)
    (inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
      (@coordinate_basisP R n) F (@coordinate_basis R m i)) <= c i.
  rewrite /c; case: (eqVneq i i0)=> [->|hNe]; first exact hSmall.
  exact: hOther.
have h := normal_jacobian_row_product_bound hRows.
have hProduct : \prod_i c i = delta.
  rewrite (bigD1 i0) //= /c eqxx.
  have -> : \prod_(i : 'I_m | i != i0) (if i == i0 then delta else 1) = 1.
    apply: big1=> i hi; by rewrite (negbTE hi).
  by rewrite mulr1.
by rewrite hProduct in h.
Qed.
