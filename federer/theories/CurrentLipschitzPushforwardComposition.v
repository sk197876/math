(** Federer (1969), 4.1.14, p. 371: the
    opaque original local images satisfy composition.
    The earlier topological lemma derives both
    intermediate support-properness facts from properness
    of the composite on spt T. Any
    evidence of those facts gives the same
    actual currents. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP MetricLocalLipschitzComposition CurrentSpaces CurrentProperSupport
  FlatCurrentsUP CurrentLipschitzPushforwardSealed CurrentLipschitzImagesComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentLipschitzPushforwardComposition.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu omega m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R omega).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R omega)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R omega)).
Variables (U:set X) (V:set Y) (W:set Z).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Hypothesis hW:forall z,W z->norm_domain_interior NZ W z.
Variables (f:X->Y) (g:Y->Z).
Hypothesis hFImage:forall x,U x->V (f x).
Hypothesis hGImage:forall y,V y->W (g y).
Hypothesis hFLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hGLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNY) (real_norm_metric_space hNZ) V g.
Local Notation gf:=(fun x=>g (f x)).
Let hGFImage:forall x,U x->W (gf x):=fun x hx=>@hGImage (f x) (@hFImage x hx).
Let hGFLocal:=@metric_local_lipschitz_composition R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY)
  (real_norm_metric_space hNZ) U V f g hFImage hFLocal hGLocal.
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_locally_flat_current R h2 n m U hU T.
Hypothesis hProperGF:@is_current_proper_on_support R h2 n omega m U hU W T gf hGFImage.
Hypothesis hProperF:@is_current_proper_on_support R h2 n nu m U hU V T f hFImage.
Local Notation Q:=(@CurrentLipschitzPushforward.value R h2 n nu m U V hU hV
  f hFImage hFLocal T hT hProperF).
Local Notation hQ:=(@CurrentLipschitzPushforward.laws R h2 n nu m U V hU hV
  f hFImage hFLocal T hT hProperF).
Hypothesis hProperG:@is_current_proper_on_support R h2 nu omega m V hV W Q g hGImage.

(** Source for [current_lipschitz_pushforward_composition]:
    (g composed f)#T=g#(f#T), Federer 4.1.14,
    p. 371. Intermediate properness proofs may
    be those derived from the single original
    composite-properness hypothesis; no global properness,
    normality or finite mass is required. *)
Theorem current_lipschitz_pushforward_composition:
  @CurrentLipschitzPushforward.value R h2 n omega m U W hU hW
    gf hGFImage hGFLocal T hT hProperGF=
  @CurrentLipschitzPushforward.value R h2 nu omega m V W hV hW
    g hGImage hGLocal Q hQ.1 hProperG.
Proof.
exact:(@current_lipschitz_images_composition R h2 n nu omega m U V W hU hV hW
  f g hFImage hGImage hFLocal hGLocal T hT hProperGF Q _ _ hQ
  (@CurrentLipschitzPushforward.laws R h2 nu omega m V W hV hW
    g hGImage hGLocal Q hQ.1 hProperG)
  (@CurrentLipschitzPushforward.laws R h2 n omega m U W hU hW
    gf hGFImage hGFLocal T hT hProperGF)).
Qed.
End CurrentLipschitzPushforwardComposition.
