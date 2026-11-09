(** Federer (1969), 3.3.4, p. 289: the
    enlarged aperture tends to zero and has bounded
    ratio to the original aperture. Prove uniform
    bounds for every solution of the independently
    specified aperture equation; no function is chosen. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals ring lra.
From Federer Require Import SignedSquareRootSealed SignedSquareRootLaws
  StructureApertureEnlargement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_enlarged_aperture_linear_bound]:
    the bounded aperture ratio used after the cone
    inclusions in Federer 3.3.4, p. 289:
    u(s)<=sqrt(k)s. The scalar root is the
    existing opaque root, and u remains any actual
    solution of the prior polynomial specification. *)
Lemma structure_enlarged_aperture_linear_bound (R:realType) k (s u:R):
  (0<k)%N ->0<s ->is_structure_enlarged_aperture k s u ->
  u<=(@SignedSquareRoot.value R (k%:R))*s.
Proof.
move=>hk hs [/andP [hu hu1] hEq].
have hK:0<=(k%:R:R) by rewrite ler0n.
have hK1:(1:R)<=k%:R by rewrite ler1n.
pose q:=@SignedSquareRoot.value R (k%:R).
have hq:0<=q:=(signed_root_sign_bounds (k%:R:R)).1 hK.
have hq2:q^+2=(k%:R:R) by rewrite /q signed_root_square (ger0_norm hK).
have hR:0<=q*s:=mulr_ge0 hq (ltW hs).
rewrite -(ler_sqr (ltW hu) hR) exprMn hq2.
have hExtra:0<=u^+2*((k%:R-1)*s^+2).
  apply:mulr_ge0; first exact:sqr_ge0.
  apply:mulr_ge0; last exact:sqr_ge0.
  by rewrite subr_ge0.
nra.
Qed.

(** Source for [structure_enlarged_aperture_small]: the
    change of aperture u(s) tends to zero in
    the finite-union cone argument of Federer 3.3.4,
    p. 289. Every solution of the exact equation
    satisfies the same all-positive-epsilon bound. *)
Theorem structure_enlarged_aperture_small (R:realType) k (e:R):
  (0<k)%N ->0<e ->exists d:R,0<d /\
    forall s u,0<s<d ->is_structure_enlarged_aperture k s u ->u<e.
Proof.
move=>hk he.
pose q:=@SignedSquareRoot.value R (k%:R).
have hq:0<=q:=(signed_root_sign_bounds (k%:R:R)).1 (ltac:(by rewrite ler0n)).
have hq1:0<q+1 by nra.
exists (e/(q+1)); split; first by rewrite divr_gt0.
move=>s u /andP [hs hSmall] hU.
have hBound:=structure_enlarged_aperture_linear_bound hk hs hU.
have hLe:q*s<=(q+1)*s.
  apply:(ler_pM hq (ltW hs)); last exact:lexx.
  by rewrite lerDl ler01.
apply:le_lt_trans (le_trans hBound hLe) _.
by move:hSmall; rewrite (ltr_pdivlMr _ _ hq1) [s*(q+1)]mulrC.
Qed.
