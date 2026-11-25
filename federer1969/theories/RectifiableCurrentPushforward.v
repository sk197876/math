(** Federer (1969), 4.1.24, p. 380: a locally
    Lipschitz map sends the original R_(m,K) into
    R_(m,g(K)). Use the original image witnesses,
    actual pushforward linearity and the existing sharp
    mass estimate on K. All compact neighbourhoods and
    finite bounds are derived; no global Lipschitz
    hypothesis on g is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet OpenLocalLipschitzCompact
  CurrentSpaces CurrentMassSealed CurrentMassBasic CurrentMassFiniteAlgebra
  FlatCurrentsUP FlatCurrentClosure
  CurrentLipschitzCompactImage CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzPushforwardBasic CurrentNormalLipschitzMassBound
  RectifiableCurrentApproximationUP RectifiableCurrentBasic RectifiableImageComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableCurrentPushforward.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable g:X->Y.
Hypothesis hImage:forall x,U x->V (g x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U g.
Variable K:smooth_compact_set hNX U.
Local Notation gK:=(@current_lipschitz_compact_image R n nu U V hU g hImage hLocal K).
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation MU:=(@CurrentMass.value R h2 n m U hU).
Local Notation MV:=(@CurrentMass.value R h2 nu m V hV).
Local Notation Push:=(@CurrentFlatLipschitzPushforward.value R h2 n nu m
  U V hU hV g hImage hLocal).
Local Notation Laws:=(@CurrentFlatLipschitzPushforward.laws R h2 n nu m
  U V hU hV g hImage hLocal).

(** Source for [rectifiable_current_lipschitz_pushforward]: the
    original locally Lipschitz image inclusion in 4.1.24,
    p. 380. The input flat witness merely types the
    already defined actual image, and may be arbitrary;
    rectifiability supplies its exact compact membership and
    finite mass. The image index is literally g(K). *)
Theorem rectifiable_current_lipschitz_pushforward (T:C)
    (hT:@is_flat_current R h2 n m U hU T):
  @is_rectifiable_current_supported_in R h2 n m U hU K T->
  @is_rectifiable_current_supported_in R h2 nu m V hV gK (Push T hT).
Proof.
move=>hRect epsilon hEpsilon.
have hTK:=@rectifiable_current_flat_supported R h2 n m U hU K T hRect.
have[L [hL hBound]]:=@norm_open_local_lipschitz_compact R X Y NX NY hNX hNY
  U g (smooth_compact_carrier K) hU hLocal (smooth_compact_is_compact K)
  (smooth_compact_in_domain K).
pose c:=L^+m.
have hc:0<=c:=exprn_ge0 m (ltW hL).
have hcOne:0<c+1 by lra.
pose delta:=epsilon/(c+1).
have hDelta:0<delta by rewrite /delta divr_gt0.
have[Q [hApprox hError]]:=hRect delta hDelta.
have hQK:@is_flat_current_supported_in R h2 n m U hU K Q.
  apply:rectifiable_current_flat_supported.
  move=>eta hEta;exists Q;split;first exact:hApprox.
  by rewrite subrr current_mass_zero lte_fin.
pose hQ:@is_flat_current R h2 n m U hU Q:=ex_intro _ K hQK.
exists (Push Q hQ);split.
- exact:(@rectifiable_image_approximant_pushforward R h2 n nu m U V hU hV
    g hImage hLocal K Q hQ hApprox).
- have hDifferenceK:@is_flat_current_supported_in R h2 n m U hU K (T-Q).
    exact:(@subspace_sub R C (@flat_current_subspace R h2 n m U hU K)
      T Q hTK hQK).
  pose hDifference:@is_flat_current R h2 n m U hU (T-Q):=
    ex_intro _ K hDifferenceK.
  have hFinite:(MU (T-Q)< +oo)%E:=lt_trans hError (ltry delta).
  have[a [ha hA]]:=@current_finite_mass_value R h2 n m U hU (T-Q) hFinite.
  have hSmall:a<delta by have h:=hError;by rewrite hA lte_fin in h.
  have hMass:=@current_flat_lipschitz_image_mass_bound R h2 n nu m U V hU hV
    g hImage hLocal K (T-Q) (Push (T-Q) hDifference) L hDifferenceK hFinite
    ((Laws (T-Q) hDifference).2 K hDifferenceK) hBound.
  have hSubtract:=@current_flat_lipschitz_pushforward_subtract
    R h2 n nu m U V hU hV g hImage hLocal T Q hT hQ hDifference.
  rewrite hSubtract hA -EFinM in hMass.
  apply:(le_lt_trans hMass);rewrite lte_fin.
  have hEnd:(c+1)*delta=epsilon by rewrite /delta mulrC divfK ?gt_eqF.
  have hBudget:c*delta<epsilon by rewrite -hEnd mulrDl mul1r;lra.
  exact:(le_lt_trans (ler_wpM2l hc (ltW hSmall)) hBudget).
Qed.
End RectifiableCurrentPushforward.
