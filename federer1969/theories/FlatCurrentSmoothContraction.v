(** Federer (1969), 4.1.17, p. 374: contraction of an
    original flat current by a smooth coefficient is flat in
    the same compact index. Use the preceding normal-current
    approximation, the actual smooth contraction and its finite
    F_K bound. This supplies the smooth side of the original
    L1 approximation proof for measurable forms. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal lra.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentContraction CurrentContractionSupport
  CurrentSupportGeometry NormalCurrentsUP NormalCurrentSmoothContraction
  CurrentFlatNorm CurrentFlatDualSeminormBasic FlatCurrentsUP
  CurrentFlatSmoothContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FlatCurrentSmoothContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Variable gamma:@current_smooth_space R h2 n U hU k.
Local Notation C := (@current_space R h2 n U hU (k+p)).
Local Notation FK := (@current_flat_norm R h2 n (k+p) U hU K).
Local Notation contract := (@current_contraction R h2 n k p U hU gamma).

(** Source for [flat_current_smooth_contraction_supported]: the
    original contraction by every smooth k-form maps F_(k+p,K)
    into F_(p,K), supporting Federer 4.1.17, p. 374. The same
    compact index, both zero-degree endpoints and zero coefficient
    constants are retained. No finite input mass is needed here. *)
Theorem flat_current_smooth_contraction_supported (T:C):
  @is_flat_current_supported_in R h2 n (k+p) U hU K T->
  @is_flat_current_supported_in R h2 n p U hU K (contract T).
Proof.
move=>hFlat epsilon hEpsilon.
have[c [hc hBound]]:=@current_smooth_contraction_flat_finite_bound
  R h2 n k p U hU K gamma.
have hDenominator:0<c+1 by lra.
pose delta:=epsilon/(c+1).
have hDelta:0<delta by rewrite /delta divr_gt0.
have[Q [hNormalQ hError]]:=hFlat delta hDelta.
have hFinite:(FK (T-Q)< +oo)%E:=lt_trans hError (ltry delta).
have[a [ha hValue]]:=@current_flat_dual_finite_value R h2 n (k+p)
  U hU K (@current_value R h2 n U hU (k+p) (T-Q)) hFinite.
change (FK (T-Q)=a%:E) in hValue.
have hRealError:a<delta by move:hError;rewrite hValue lte_fin.
have hOutput:=hBound (T-Q) a hValue.
have hSmall:c*a<epsilon.
  have hFirst:=ler_wpM2l hc (ltW hRealError).
  have hStrict:c*delta<(c+1)*delta.
    rewrite (ltr_pM2r hDelta);lra.
  have hEndpoint:(c+1)*delta=epsilon.
    by rewrite /delta mulrC divfK ?gt_eqF.
  rewrite hEndpoint in hStrict;exact:le_lt_trans hFirst hStrict.
exists (contract Q);split.
- split.
  + exact:(@normal_current_smooth_contraction R h2 n U hU k p gamma Q hNormalQ.1).
  + move=>x hx;apply:hNormalQ.2.
    exact:(@current_contraction_support_subset R h2 n k p U hU gamma Q x hx).
- rewrite -(linB (hom_linear contract)).
  apply:(le_lt_trans hOutput);by rewrite lte_fin.
Qed.
End FlatCurrentSmoothContraction.
