(** Federer (1969), 3.2.11, p. 249: the
    norm bound on Dg also bounds Dg*. This supporting
    implication is precisely the adjoint norm equality of
    1.7.6, p. 33, applied through its abstract norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm EuclideanRectangularAdjoint OperatorNormUP OperatorNorm OperatorNormLaws OperatorNormAdjoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_rectangular_adjoint_bound]: supporting
    |Dg* a| <= (Lip f+epsilon)|a| in Federer 3.2.11,
    p. 249. A nonnegative homogeneous bound for a
    Euclidean linear map bounds its actual sealed adjoint,
    with no dimensional or injectivity restriction. *)
Theorem euclidean_rectangular_adjoint_bound (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)) C:
  0<=C ->(forall x,inner_norm (@euclidean_inner_productP R n) (D x)<=
    C*inner_norm (@euclidean_inner_productP R m) x) ->
  forall y,inner_norm (@euclidean_inner_productP R m) (euclidean_rectangular_adjoint D y)<=
    C*inner_norm (@euclidean_inner_productP R n) y.
Proof.
move=>hC hBound.
pose hX:=@euclidean_inner_productP R m.
pose hY:=@euclidean_inner_productP R n.
pose A:=euclidean_rectangular_adjoint D.
pose L:=linear_operator_norm hX hY (@coordinate_basisP R m) (hom_as_linear D).
pose M:=linear_operator_norm hY hX (@coordinate_basisP R n) (hom_as_linear A).
have hL:=linear_operator_normP hX hY (@coordinate_basisP R m) (hom_as_linear D).
have hM:=linear_operator_normP hY hX (@coordinate_basisP R n) (hom_as_linear A).
have hLC:L<=C.
  apply:(operator_norm_le_unit hL C).2=>x hx.
  apply:le_trans (hBound x) _.
  by have h:=ler_wpM2l hC hx; rewrite mulr1 in h.
have hEqual:L=M:=operator_norm_adjoint_equal (euclidean_rectangular_adjoint_pairing D) hL hM.
move=>y.
have hVal:=@operator_norm_vector_bound R (R_n R n) (R_n R m)
  (@euclidean_inner_product R n) (@euclidean_inner_product R m) hY hX
  (hom_as_linear A) M hM y.
rewrite -hEqual in hVal.
exact (le_trans hVal (ler_wpM2r (inner_norm_nonnegative hY y) hLC)).
Qed.
