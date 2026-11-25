(** Federer (1969), 3.2.31, p. 269: the homogeneous
    half-contraction laws imply the printed strict unit bound
    for the actual ordinary norm of the inverse-rescaled map. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm OperatorNormUP OperatorNorm OperatorNormLaws SmallExteriorMajorantUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [small_exterior_majorant_strict_inverse_norm]:
    the printed norm(t^-1 D)<1 condition in Federer 3.2.31,
    p. 269, derived from the independent stronger half-contraction
    laws. The norm is the actual operator norm of the actual
    composed linear map. No numerical bound is supplied by
    an unproved additional geometric premise. *)
Lemma small_exterior_majorant_strict_inverse_norm (R:realType) m v mu
    (D:Hom (R_n R m) (R_n R v)) (epsilon:R)
    (T U:Hom (R_n R v) (R_n R v)):
  @is_small_exterior_majorant R m v mu D epsilon T U ->
  linear_operator_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R v)
    (@coordinate_basisP R m) (linear_comp (hom_as_linear U) (hom_as_linear D))<1.
Proof.
move=>hMajorant.
pose f:=linear_comp (hom_as_linear U) (hom_as_linear D).
pose L:=linear_operator_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R v)
  (@coordinate_basisP R m) f.
have hNorm:is_operator_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R v) f L:=
  linear_operator_normP (@euclidean_inner_productP R m) (@euclidean_inner_productP R v)
    (@coordinate_basisP R m) f.
have hTwo:(0<(2:R)) by rewrite ltr0n.
have hHalf:(0<(1/2:R)) by rewrite divr_gt0.
have hBound:L<=1/2.
  apply:(operator_norm_le_unit hNorm (1/2)).2=>x hx.
  change (is_true (inner_norm (@euclidean_inner_productP R v) (U (D x))<=1/2)).
  have hPoint:=@small_exterior_majorant_contraction R m v mu D epsilon T U hMajorant x.
  have hScale:=ler_wpM2l (ltW hHalf) hx.
  rewrite mulr1 in hScale.
  exact (le_trans hPoint hScale).
have hHalfOne:(1/2:R)<1.
  by rewrite (@ltr_pdivrMr R 2 1 1 hTwo) mul1r ltr1n.
exact (le_lt_trans hBound hHalfOne).
Qed.
