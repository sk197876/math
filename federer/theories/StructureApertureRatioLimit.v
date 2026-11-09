(** Federer (1969), 3.3.4, p. 289:
    the precise enlarged-aperture ratio tends
    to sqrt(k). Uniform estimates apply to
    every solution of the prior polynomial
    aperture specification; no global solution
    function or root implementation is selected. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals ring lra.
From Federer Require Import SignedSquareRootSealed SignedSquareRootLaws
  StructureApertureEnlargement StructureApertureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_enlarged_aperture_ratio_error]:
    supporting the printed limit u(s)/s to
    sqrt(k) in Federer 3.3.4, p. 289.
    The actual ratio lies below sqrt(k),
    and its gap is at most sqrt(k)(k-1)s^2. *)
Lemma structure_enlarged_aperture_ratio_error (R:realType) k (s u:R):
  (0<k)%N ->0<s ->is_structure_enlarged_aperture k s u ->
  0<=(@SignedSquareRoot.value R k%:R)-u/s<=
    (@SignedSquareRoot.value R k%:R)*(k%:R-1)*s^+2.
Proof.
move=>hk hs hU.
pose q:=@SignedSquareRoot.value R k%:R.
pose v:=u/s.
have hK:0<(k%:R:R) by rewrite ltr0n.
have hK1:(1:R)<=k%:R by rewrite ler1n.
have hQ0:0<=q:=(signed_root_sign_bounds (k%:R:R)).1 (ltW hK).
have hQ2:q^+2=(k%:R:R) by rewrite /q signed_root_square (ger0_norm (ltW hK)).
have hQ:0<q by nra.
have hUPositive:0<u:=(andP hU.1).1.
have hV:0<v by rewrite /v divr_gt0.
have hVQ:v<=q.
  rewrite /v (ler_pdivrMr _ _ hs).
  exact:structure_enlarged_aperture_linear_bound hk hs hU.
have hEquation:v^+2*(1+(k%:R-1)*s^+2)=(k%:R:R).
  by rewrite /v exprMn exprVn mulrAC hU.2 mulfK ?expf_neq0 ?gt_eqF.
have hSquares:v^+2<=q^+2 by nra.
have hC:0<=(k%:R:R)-1 by rewrite subr_ge0.
have hRight:v^+2*((k%:R-1)*s^+2)<=q^+2*((k%:R-1)*s^+2).
  apply:ler_wpM2r=>//; exact:mulr_ge0 hC (sqr_ge0 s).
have hGap:q-v<=q*(k%:R-1)*s^+2 by nra.
apply/andP; split; first by rewrite subr_ge0.
exact:hGap.
Qed.

(** Source for [structure_enlarged_aperture_ratio_limit]:
    the exact limit u(s)/s=sqrt(k) as
    s tends to zero from above in Federer
    3.3.4, p. 289. Every solution has
    arbitrarily small absolute ratio error at
    all sufficiently small positive real apertures. *)
Theorem structure_enlarged_aperture_ratio_limit (R:realType) k (e:R):
  (0<k)%N ->0<e ->exists d:R,0<d /\ forall s u,
    0<s<d ->is_structure_enlarged_aperture k s u ->
    `|u/s-(@SignedSquareRoot.value R k%:R)|<e.
Proof.
move=>hk he.
pose q:=@SignedSquareRoot.value R k%:R.
pose C:=q*(k%:R-1).
have hQ:0<=q:=(signed_root_sign_bounds (k%:R:R)).1 (ltac:(by rewrite ler0n)).
have hK1:(1:R)<=k%:R by rewrite ler1n.
have hC:0<=C by rewrite /C mulr_ge0 // subr_ge0.
have hC1:0<C+1 by nra.
exists (Num.min 1 (e/(C+1))); split; first by rewrite lt_min ltr01 divr_gt0.
move=>s u /andP [hs hSmall] hU.
have /andP [hs1 hsE]:(s<1)&&(s<e/(C+1)) by move:hSmall; rewrite lt_min.
have /andP [hGap0 hGap]:=structure_enlarged_aperture_ratio_error hk hs hU.
rewrite distrC (ger0_norm hGap0).
have hSquare:s^+2<=s by nra.
have hBound:C*s^+2<=(C+1)*s by nra.
have hStrict:(C+1)*s<e by move:hsE; rewrite (ltr_pdivlMr _ _ hC1) mulrC.
exact:le_lt_trans (le_trans hGap hBound) hStrict.
Qed.
