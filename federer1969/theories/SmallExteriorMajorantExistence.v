(** Federer (1969), 3.2.31, p. 269: choose a symmetric
    automorphism t with arbitrarily small mu-th exterior norm
    and norm(t^-1 D)<1 when rank D<mu. Prove all required
    witnesses through independent projection, scaling and norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerProductUP
  InnerNorm InnerNormalization LinearBasis OrthonormalFamilies EigenbasisUP SymmetricEigenbasis
  OperatorNormUP OperatorNorm LinearRankAtLeast SymmetricRangeIdempotentUP SymmetricRangeIdempotentExistence
  ProjectionScaleAutomorphismUP ProjectionScaleAutomorphismExistence ProjectionScaleInverseDerivativeBound
  ProjectionScaleExteriorBound SmallExteriorMajorantUP SmallExteriorMajorantScalars IdempotentEigenvalueAlternatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [small_exterior_majorant_exists]: the actual
    small symmetric automorphism selected in Federer 3.2.31,
    p. 269. Use a symmetric idempotent for the true range,
    diagonalize it by 1.7.3, and put a large scale on the
    range and a positive small scale on its complement.
    Rank below mu forces a small factor in every exterior
    word. The actual exterior norm and inverse-derivative
    half-contraction are proved, not assumed. No source/target
    dimension comparison or globally chosen map is introduced.
    The rank-deficiency premise is impossible in degree zero. *)
Theorem small_exterior_majorant_exists (R:realType) m v mu
    (D:Hom (R_n R m) (R_n R v)) (epsilon:R):
  ~linear_rank_at_least D mu ->0<epsilon ->
  exists T U,@is_small_exterior_majorant R m v mu D epsilon T U.
Proof.
move=>hRank heps.
have [P hP]:=@symmetric_range_idempotent_exists R (R_n R m) (R_n R v)
  (@euclidean_inner_product R v) (@euclidean_inner_productP R v)
  v (@coordinate_basis R v) (@coordinate_basisP R v) D.
have hSym:=@range_idempotent_symmetric R (R_n R m) (R_n R v) (@euclidean_inner_product R v) D P hP.
have hIdem:=@range_idempotent_idempotent R (R_n R m) (R_n R v) (@euclidean_inner_product R v) D P hP.
have [e [beta hEigen]]:=@symmetric_orthonormal_eigenbasis R (R_n R v)
  (@euclidean_inner_product R v) (@euclidean_inner_productP R v) (hom_as_linear P)
  hSym v (@coordinate_basis R v) (@coordinate_basisP R v).
have hBasis:is_basis e:=eigenbasis_basis hEigen.
have hE:orthonormal_family (@euclidean_inner_product R v) e:=eigenbasis_orthonormal hEigen.
have hEV i:P (e i)=beta i*:e i:=@eigenbasis_eigenvalue R (R_n R v)
  (@euclidean_inner_product R v) (hom_as_linear P) v e beta hEigen i.
have hNonzero i:e i!=0.
  apply/eqP=>hz.
  have hh:=@orthonormal_norm1 R (R_n R v) (@euclidean_inner_product R v)
    (@euclidean_inner_productP R v) [the finType of 'I_v] e hE i.
  rewrite hz inner_norm0 in hh.
  by move:hh=>/eqP; rewrite eq_sym oner_eq0.
have hBinary i:beta i=0 \/beta i= 1.
  exact (@idempotent_eigenvalue_zero_or_one R (R_n R v) P (e i) (beta i)
    hIdem (hNonzero i) (hEV i)).
pose c:=linear_operator_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R v)
  (@coordinate_basisP R m) (hom_as_linear D).
have hNorm:is_operator_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R v)
    (hom_as_linear D) c:=linear_operator_normP (@euclidean_inner_productP R m)
      (@euclidean_inner_productP R v) (@coordinate_basisP R m) (hom_as_linear D).
have hc:0<=c:=operator_norm_nonnegative hNorm.
have [M [d [hM1 [hd [hd1 [hRatio hSmall]]]]]]:=@small_exterior_majorant_scalars R c epsilon mu hc heps.
have hM:0<M:=lt_le_trans ltr01 hM1.
have hMn:M!=0 by rewrite gt_eqF.
have hdn:d!=0 by rewrite gt_eqF.
have [T [U hScale]]:=@projection_scale_automorphism_exists R (R_n R v)
  (@euclidean_inner_product R v) (inner_bilinear (@euclidean_inner_productP R v))
  P M d hSym hIdem hMn hdn.
exists T,U; constructor.
- exact:projection_scale_symmetric hScale.
- exact:projection_scale_left_inverse hScale.
- exact:projection_scale_right_inverse hScale.
- have hh:=@projection_scale_exterior_bound R m v mu D P M d T U e hBasis hE beta
    hP hScale hEV hBinary hRank hM1 hd hd1.
  exact (le_lt_trans hh hSmall).
- exact (@projection_scale_inverse_derivative_bound R m v D P M d T U c hP hScale hNorm hM hRatio).
Qed.
