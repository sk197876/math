(** Federer (1969), 3.4.8(11), p. 335:
    |p_(j+1)(x)| is at most |p_j(x)|
    plus |omega_(j+1)(x)|. The actual
    adjacent-prefix equation and the already proved
    last-coordinate transverse split give this estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness OrthonormalFamilies InnerNormalization EuclideanStiefelInnerSplitting
  EuclideanScalarCoordinateMaps AnalyticPrefixCoordinatesUP AnalyticPrefixCoordinatesSealed
  AnalyticPrefixNestedComposition AnalyticPrefixWeierstrassSplit WeierstrassSplitNormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_prefix_norm_step]:
    the final strict prefix bound in
    the clopen-neighbourhood proof, 3.4.8(11), p. 335. *)
Theorem analytic_prefix_norm_step (R:realType) (X:lmodType R) n
    (omega:'I_n->Hom X R^o) j (hJN:(j<=n)%N) (hJ1N:(j.+1<=n)%N)
    (P:Hom X (R_n R j)) (Q:Hom X (R_n R j.+1)):
  is_analytic_prefix_projection omega hJN P ->
  is_analytic_prefix_projection omega hJ1N Q ->
  forall x,inner_norm (@euclidean_inner_productP R j.+1) (Q x)<=
    inner_norm (@euclidean_inner_productP R j) (P x)+`|omega (Ordinal hJ1N) x|.
Proof.
move=>hP hQ x.
pose Y:=R_n R j.+1.
pose NY:=inner_norm (@euclidean_inner_productP R j.+1).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R j.+1).
pose omegaY:=fun i:'I_j.+1=>@euclidean_scalar_coordinate_map R j.+1 i.
pose between:=@AnalyticPrefixCoordinates.projection R Y j.+1 omegaY j (leqnSn j).
pose section:=@AnalyticPrefixCoordinates.inclusion R Y j.+1 (@coordinate_basis R j.+1) j (leqnSn j).
have hBetween:=@AnalyticPrefixCoordinates.projection_laws R Y j.+1 omegaY j (leqnSn j).
have hSection:=@AnalyticPrefixCoordinates.inclusion_laws R Y j.+1 (@coordinate_basis R j.+1) j (leqnSn j).
have hDual i l:omegaY i (@coordinate_basis R j.+1 l) = if i==l then 1 else 0.
  by rewrite /omegaY /euclidean_scalar_coordinate_map /= /coordinate_basis ffunE eq_sym.
have hSplit:=@analytic_last_coordinate_prefix_split R Y (@euclidean_inner_product R j.+1)
  (@euclidean_inner_productP R j.+1) j (@coordinate_basis R j.+1) (@coordinate_basisP R j.+1)
  (@euclidean_coordinate_orthonormal_family R j.+1) omegaY hDual between section hBetween hSection.
have hUnit:NY (@coordinate_basis R j.+1 ord_max) = 1.
  exact:(@orthonormal_norm1 R Y (@euclidean_inner_product R j.+1)
    (@euclidean_inner_productP R j.+1) (Finite.clone 'I_j.+1 _)
    (@coordinate_basis R j.+1) (@euclidean_coordinate_orthonormal_family R j.+1) ord_max).
have hBound:=@weierstrass_split_norm_bound R Y (R_n R j) NY
  (inner_norm (@euclidean_inner_productP R j)) hNY (@coordinate_basis R j.+1 ord_max)
  (omegaY ord_max) section between hSplit hUnit (Q x).
have hComposition:=@analytic_adjacent_prefix_composition R X n omega j hJN hJ1N
  P Q between hP hQ hBetween x.
rewrite -hComposition in hBound.
have hLast:omegaY ord_max (Q x) = omega (Ordinal hJ1N) x.
  change (Q x ord_max = omega (Ordinal hJ1N) x).
  rewrite hQ;congr (omega _ x);apply:val_inj;by [].
by rewrite hLast in hBound.
Qed.
