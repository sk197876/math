(** Expanded continuity support for Federer (1969), 3.2.45,
    p. 279: the actual scalar rows are controlled by the existing
    operator and Hom norms, without a new matrix norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  EuclideanCoordinateMetric Adjoint AdjointUP OperatorNormUP OperatorNorm OperatorNormAdjoint
  HomInner HomNormBound EuclideanRowFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_adjoint_row_hom_norm_bound]: expanded
    support for Federer 3.2.45, p. 279, from adjoint norm
    equality, 1.7.6, p. 33, and operator norm <= Hom norm,
    1.7.9, p. 35. Each standard coordinate vector has norm one;
    its actual adjoint image is the scalar row. *)
Lemma euclidean_adjoint_row_hom_norm_bound (R : realType) n m
    (F : Hom (R_n R n) (R_n R m)) (i : 'I_m) :
  inner_norm (@euclidean_inner_productP R n)
    (inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
      (@coordinate_basisP R n) (hom_as_linear F) (@coordinate_basis R m i)) <=
    hom_norm (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
      (@coordinate_basisP R n) F.
Proof.
pose A := inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
  (@coordinate_basisP R n) (hom_as_linear F).
have hA := @inner_adjointP R (R_n R n) (R_n R m)
  (@euclidean_inner_product R n) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n) (hom_as_linear F).
have hFNorm := linear_operator_normP (@euclidean_inner_productP R n)
  (@euclidean_inner_productP R m) (@coordinate_basisP R n) (hom_as_linear F).
have hANorm := linear_operator_normP (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R n) (@coordinate_basisP R m) A.
have hEqual := operator_norm_adjoint_equal hA hFNorm hANorm.
have hUnit : inner_norm (@euclidean_inner_productP R m) (@coordinate_basis R m i) <= 1.
  by rewrite euclidean_coordinate_unit_norm.
have hBound := operator_norm_unit_bound hANorm hUnit.
rewrite -hEqual in hBound.
apply: le_trans hBound _.
exact: (@operator_norm_le_hom_norm R (R_n R n) (R_n R m)
  (@euclidean_inner_product R n) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n) F _ hFNorm).
Qed.

(** Source for [euclidean_row_family_hom_norm_bound]: the same
    actual row bound through the independent row laws, supporting
    Federer 3.2.45, p. 279. This is a public-interface connection;
    it does not inspect the adjoint or Hom construction. *)
Corollary euclidean_row_family_hom_norm_bound (R : realType) n m
    (v : 'I_m -> R_n R n) (F : Hom (R_n R n) (R_n R m)) :
  is_euclidean_row_family v (hom_as_linear F) -> forall i,
  inner_norm (@euclidean_inner_productP R n) (v i) <=
    hom_norm (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
      (@coordinate_basisP R n) F.
Proof.
move=> hRows i.
rewrite -(euclidean_row_family_adjoint hRows i).
exact: euclidean_adjoint_row_hom_norm_bound.
Qed.
