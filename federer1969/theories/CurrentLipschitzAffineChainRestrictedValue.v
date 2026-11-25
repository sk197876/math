(** Federer (1969), 4.1.14, pp. 371–372: compute
    the original affine chain on a nested source
    neighbourhood. Exact zero-extension restriction and
    the original flat-image congruence preserve the
    actual chain; no support-index coincidence is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces FlatCurrentsUP CurrentOpenRestriction
  CurrentOpenRestrictionSupport CurrentOpenRestrictionTransitive
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentAffineHomotopySealed
  CurrentLipschitzAffineChainUP CurrentAffineNeighbourhoodProductFlat
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  CurrentFlatLipschitzProofIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLipschitzAffineChainRestrictedValue.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Hypotheses (hFLocal:@is_locally_metric_lipschitz R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f)
  (hGLocal:@is_locally_metric_lipschitz R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY) U g).
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current R h2 n m U hU T.
Variable Q:@current_space R h2 nu V hV (1+m)%N.
Hypothesis hQ:@is_current_lipschitz_affine_chain R h2 n nu m U V hU hV
  f g hFLocal hGLocal T Q.
Variable W0:set X.
Hypothesis hW0:forall x,W0 x->norm_domain_interior NX W0 x.
Hypothesis hW0U:forall x,W0 x->U x.
Hypothesis hSupport0:@current_support R h2 n U hU m T `<=` W0.
Local Notation S0 := (@current_open_restriction R h2 n m W0 U hW0 hU hW0U T).
Variable A:set R.
Hypothesis hA:@is_homotopy_parameter_interval R A.
Variable W1:set X.
Hypothesis hW1:forall x,W1 x->norm_domain_interior NX W1 x.
Hypothesis hW1W0:forall x,W1 x->W0 x.
Hypothesis hSupport1:@current_support R h2 n W0 hW0 m S0 `<=` W1.
Hypothesis hBand:forall t x,A t->W1 x->V ((1-t)*:f x+t*:g x).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hA).
Local Notation AW := (@current_homotopy_product_domain R n A W1).
Local Notation hAW := (@current_cartesian_domain_open R 1%N n AT W1 hAT hW1).
Local Notation H := (@CurrentAffineHomotopy.value R n nu f g).
Hypothesis hImage:forall z,AW z->V (H z).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)))
  (real_norm_metric_space hNY) AW H.
Local Notation S1 := (@current_open_restriction R h2 n m W1 W0 hW1 hW0 hW1W0 S0).
Local Notation P := (@CartesianCurrentProduct.value R h2 1%N n 1%N m AT W1 hAT hW1
  (@current_homotopy_time_segment R A hA h2) S1).
Hypothesis hP:@is_flat_current R h2 (1+n)%N (1+m)%N AW hAW P.

(** Source for [current_lipschitz_affine_chain_restricted_value]:
    any nested original neighbourhood computes the same
    affine chain, supporting Federer 4.1.14, pp. 371–372.
    Only spt T must lie in W0; the next
    source need contain only the restricted support. *)
Theorem current_lipschitz_affine_chain_restricted_value :
  Q=@CurrentFlatLipschitzPushforward.value R h2 (1+n)%N nu (1+m)%N
    AW V hAW hV H hImage hLocal P hP.
Proof.
pose hW1U:=fun x hx=>@hW0U x (@hW1W0 x hx).
have hSupportLarge:@current_support R h2 n U hU m T `<=` W1.
  move=>x hx;apply:hSupport1.
  rewrite current_open_restriction_support.
  exact:conj (@hSupport0 x hx) hx.
pose Pdirect:=@current_affine_neighbourhood_product R h2 n m A hA U W1
  hU hW1 hW1U T.
pose hPdirect:=@current_affine_neighbourhood_product_flat R h2 n m A hA
  U W1 hU hW1 hW1U T hFlat hSupportLarge.
pose hImageDirect:=@current_affine_neighbourhood_image R n nu A W1 V f g hBand.
pose hLocalDirect:=@current_affine_neighbourhood_local R n nu U W1 hW1 hW1U
  f g hFLocal hGLocal A hA.
have hQdirect:=hQ.2 A hA W1 hW1 hW1U hSupportLarge hBand hPdirect.
have hTransitive:=@current_open_restriction_transitive R h2 n m W1 W0 U
  hW1 hW0 hU hW1W0 hW0U hW1U T.
have hProduct:Pdirect = P.
  rewrite /Pdirect /current_affine_neighbourhood_product.
  by rewrite -hTransitive.
have hFirst:=@current_flat_lipschitz_pushforward_congruence R h2 (1+n)%N nu
  (1+m)%N AW V hAW hV H hImageDirect hLocalDirect Pdirect P hPdirect hP hProduct.
have hSecond:=@current_flat_lipschitz_pushforward_data_independent R h2
  (1+n)%N nu (1+m)%N AW V hAW hV H hImageDirect hImage hLocalDirect hLocal P hP hP.
exact:eq_trans hQdirect (eq_trans hFirst hSecond).
Qed.
End CurrentLipschitzAffineChainRestrictedValue.
