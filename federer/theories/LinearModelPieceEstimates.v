(** Federer (1969), 3.2.2, p. 242: the differential
    vector and Jacobian estimates, univalence and two Lipschitz
    bounds on every sufficiently small Borel subset of Z(s,i). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric RealNormUP NormDifferentialUP
  NormDifferentialDirectional EuclideanLinearMaps EuclideanLinearJacobian
  LinearModelLocus LinearModelRemainderBounds RelativeLowerInjectivity
  LinearJacobianPrecomposition FiniteLinearInverseField PartialFunctionUP
  RestrictedInverseExistence InjectiveDifferentialPieceUP TopologicalBorel LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Estimates.
Variable R:realType.
Variables m n:nat.
Variable f:R_n R m->R_n R n.
Variable s:Hom (R_n R m) (R_n R m).
Variables lambda e:R.
Variable i:nat.
Let NX:=inner_norm (@euclidean_inner_productP R m).
Let NY:=inner_norm (@euclidean_inner_productP R n).
Let hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
Let hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).

(** Source for [linear_model_locus_differential_bounds]: the
    first condition on Z(s,i), Federer 3.2.2, p. 242,
    holds for the unique actual differential, regardless of
    which witness supplied membership. *)
Lemma linear_model_locus_differential_bounds a D:
  linear_model_locus f s lambda e i a ->
  has_norm_differential NX NY setT f a D ->
  (forall v,(lambda^-1+e)*NX (s v)<=NY (D v) /\ NY (D v)<=(lambda-e)*NX (s v)) /\
  (forall h,NX h<=(i.+1%:R:R)^-1 -> NY (f (a+h)-f a-D h)<=e*NX (s h)).
Proof.
move=>[T [hT [hVec hRem]]] hD.
have heq:T=D:=norm_differential_unique hNX hNY hT hD.
by subst T; split.
Qed.

(** Source for [linear_model_locus_injective]: the first
    condition on Z(s,i) forces an injective differential,
    Federer 3.2.2, p. 242. The positive lower margin
    and injective source model are retained explicitly. *)
Lemma linear_model_locus_injective:
  injective s -> 0<lambda -> 0<e ->
  linear_model_locus f s lambda e i `<=` injective_differential_locus f.
Proof.
move=>hs hl he a [D [hD [hVec hRem]]].
exists D; split; first exact hD.
have hi:0<lambda^-1 by rewrite invr_gt0.
have hc:0<lambda^-1+e by nra.
exact (linear_relative_lower_injective hNX hNY hs hc (fun v=>(hVec v).1)).
Qed.

(** Source for [linear_model_locus_pair_bounds]: the two
    displayed estimates for a,b in E, Federer 3.2.2,
    p. 242. The diameter bound places each increment in
    the closed ball used in the remainder condition. *)
Lemma linear_model_locus_pair_bounds (E:set (R_n R m)):
  E `<=` linear_model_locus f s lambda e i ->
  (forall a b,E a -> E b -> NX (a-b)<=(i.+1%:R:R)^-1) ->
  forall a b,E a -> E b ->
    lambda^-1*NX (s (a-b))<=NY (f a-f b) /\
    NY (f a-f b)<=lambda*NX (s (a-b)).
Proof.
move=>hE hDiam a b ha hb.
have [D [hD [hVec hRem]]]:=hE b hb.
have hR:=hRem (a-b) (hDiam a b ha hb).
rewrite (addrC b (a-b)) subrK in hR.
exact (linear_model_remainder_bounds hNY (hVec (a-b)).1 (hVec (a-b)).2 hR).
Qed.

(** Source for [linear_model_small_piece]: all properties of
    a small Borel E contained in Z(s,i), Federer 3.2.2,
    p. 242. The inverse is proved to exist on exactly
    f(E); vector estimates imply the Jacobian bounds through
    exterior powers and the source determinant. *)
Theorem linear_model_small_piece (E:set (R_n R m)):
  1<lambda -> 0<e -> injective s ->
  @borel_set [the topologicalType of real_norm_metric_space hNX] E ->
  E `<=` linear_model_locus f s lambda e i ->
  (forall a b,E a -> E b -> NX (a-b)<=(i.+1%:R:R)^-1) ->
  is_injective_differential_piece f lambda E.
Proof.
move=>hl he hs hB hE hDiam.
have hl0:0<lambda:=lt_trans ltr01 hl.
have hInv:0<lambda^-1 by rewrite invr_gt0.
have hPair:=linear_model_locus_pair_bounds hE hDiam.
have hInj:{in E &,injective f}.
  exact (relative_lower_bound_injective hNX hNY hs hInv (fun a b ha hb=>(hPair a b ha hb).1)).
split; first exact hB.
split.
- move=>a ha; exact (linear_model_locus_injective hs hl0 he (hE a ha)).
split; first exact hInj.
have [t [hst hts]]:=finite_injective_linear_inverse_exists (@coordinate_basisP R m) hs.
have [g hg]:=restricted_inverse_graph_exists hInj.
exists s,t,g; split; first exact hst.
split; first exact hts.
split; first exact hg.
split.
- split; first exact (ltW hl0).
  move=>x y [a ha <-] [b hb <-].
  change (is_true (NY (f (t (s a))-f (t (s b)))<=lambda*NX (s a-s b))).
  rewrite !hst -linearB; exact (hPair a b ha hb).2.
split.
- move=>y z x w /hg [hx <-] /hg [hw <-].
  change (is_true (NX (s x-s w)<=lambda*NY (f x-f w))).
  rewrite -linearB.
  have hh:=ler_wpM2l (ltW hl0) (hPair x w hx hw).1.
  by rewrite mulrA mulfV ?mul1r in hh; first exact hh; rewrite gt_eqF.
- move=>x hx D hD.
  have [hVec hRem]:=linear_model_locus_differential_bounds (hE x hx) hD.
  have hWeak v:lambda^-1*NX (s v)<=NY (D v) /\ NY (D v)<=lambda*NX (s v).
    have hn:0<=NX (s v):=inner_norm_nonnegative (@euclidean_inner_productP R m) (s v).
    have [hLower hUpper]:=hVec v; split; nra.
  split; first exact hWeak.
  exact (euclidean_relative_jacobian_sandwich hst hts (ltW hInv) (ltW hl0)
    (fun v=>(hWeak v).1) (fun v=>(hWeak v).2)).
Qed.
End Estimates.
