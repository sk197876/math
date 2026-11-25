(** Federer (1969), 4.1.14, pp. 371–372: the
    actual affine chain depends on the original current
    and maps, rather than proofs of their original
    hypotheses. Use the independently proved uniqueness law;
    never unfold the opaque chosen value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces FlatCurrentsUP CurrentLipschitzAffineChainUP
  CurrentLipschitzAffineChainExistence CurrentLipschitzAffineChainSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentLipschitzAffineChainBasic.
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
Variables f g:X->Y.
Hypothesis hFLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hGLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U g.
Variable T:@current_space R h2 n U hU m.
Local Notation Flat:=(@is_flat_current R h2 n m U hU T).
Local Notation Band:=(forall t x,0<=t<=1->@current_support R h2 n U hU m T x->
  V ((1-t)*:f x+t*:g x)).

(** Source for [current_lipschitz_affine_chain_proof_independent]:
    the original affine chain is independent of
    flat-membership and support-segment evidence, supporting
    Federer 4.1.14, pp. 371–372. Both actual
    values satisfy the same independent neighbourhood law. *)
Theorem current_lipschitz_affine_chain_proof_independent
    (hFlat hFlat':Flat) (hBand hBand':Band):
  @CurrentLipschitzAffineChain.value R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat hBand=
  @CurrentLipschitzAffineChain.value R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat' hBand'.
Proof.
exact:(@current_lipschitz_affine_chain_unique R h2 n nu m U V hU hV
  f g hFLocal hGLocal T hFlat hBand
  (@CurrentLipschitzAffineChain.value R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat hBand)
  (@CurrentLipschitzAffineChain.value R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat' hBand')
  (@CurrentLipschitzAffineChain.laws R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat hBand)
  (@CurrentLipschitzAffineChain.laws R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat' hBand')).
Qed.

(** Source for [current_lipschitz_affine_chain_data_independent]:
    presenting the same local Lipschitz hypotheses by
    different proofs does not change the actual
    affine chain of Federer 4.1.14, pp. 371–372.
    This changes only evidence, never a map or current. *)
Theorem current_lipschitz_affine_chain_data_independent
    (hFLocal':@is_locally_metric_lipschitz R
      (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f)
    (hGLocal':@is_locally_metric_lipschitz R
      (real_norm_metric_space hNX) (real_norm_metric_space hNY) U g)
    (hFlat hFlat':Flat) (hBand hBand':Band):
  @CurrentLipschitzAffineChain.value R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat hBand=
  @CurrentLipschitzAffineChain.value R h2 n nu m U V hU hV
    f g hFLocal' hGLocal' T hFlat' hBand'.
Proof.
have hFirst:hFLocal'=hFLocal:=Prop_irrelevance _ _.
have hSecond:hGLocal'=hGLocal:=Prop_irrelevance _ _.
subst hFLocal' hGLocal'.
exact:(@current_lipschitz_affine_chain_proof_independent hFlat hFlat' hBand hBand').
Qed.
End CurrentLipschitzAffineChainBasic.

Arguments current_lipschitz_affine_chain_proof_independent : clear implicits.
Arguments current_lipschitz_affine_chain_data_independent : clear implicits.
