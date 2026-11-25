(** Federer (1969), 3.3.4, p. 289: specify the
    enlarged aperture u(s) before proving its existence.
    Witnesses remain local; the only square root used
    is the previously sealed scalar square root. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals ring lra.
From Federer Require Import SignedSquareRootSealed SignedSquareRootLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_structure_enlarged_aperture]: the
    printed equation for u(s) in Federer 3.3.4,
    p. 289, equivalently written without inverse
    powers. The integer k is the positive codimension
    n-m; u is required to remain in the original
    aperture range (0,1). *)
Definition is_structure_enlarged_aperture (R:realType) k (s u:R):Prop:=
  0<u<1 /\ u^+2*(1+(k%:R-1)*s^+2)=k%:R*s^+2.

(** Source for [structure_enlarged_aperture_exists]: actual
    positive-aperture existence in Federer 3.3.4,
    p. 289. Its scalar square root serves only
    as a local existence witness for the prior equation. *)
Theorem structure_enlarged_aperture_exists (R:realType) k (s:R):
  (0<k)%N ->0<s<1 ->exists u,is_structure_enlarged_aperture k s u.
Proof.
move=>hk /andP [hs hs1].
have hK:0<(k%:R:R) by rewrite ltr0n.
have hK1:(1:R)<=k%:R by rewrite ler1n.
have hs2:0<s^+2 by rewrite exprn_gt0.
have hs21:s^+2<1 by nra.
pose b:=(1+(k%:R-1)*s^+2:R).
have hb:0<b by rewrite /b; nra.
pose q:=(k%:R*s^+2/b:R).
have hq:0<q by rewrite /q divr_gt0 // mulr_gt0.
have hq1:q<1 by rewrite /q (ltr_pdivrMr _ _ hb) mul1r /b; nra.
pose u:=@SignedSquareRoot.value R q.
have hu0:0<=u:=(signed_root_sign_bounds q).1 (ltW hq).
have hu2:u^+2=q by rewrite /u signed_root_square (ger0_norm (ltW hq)).
have hu:0<u.
  rewrite lt_def hu0 andbT; apply/negP=>he.
  have huZero:u=0:=eqP he.
  have hqZero:q=0 by rewrite -hu2 huZero expr0n.
  by move:hq; rewrite hqZero ltxx.
have hu1:u<1 by rewrite -(ltr_sqr hu0 ler01) expr1n hu2.
exists u; split; first by apply/andP.
by rewrite -/b hu2 /q divfK ?gt_eqF.
Qed.

(** Source for [structure_enlarged_aperture_inverse_equation]:
    the exact printed inverse-square equation in
    Federer 3.3.4, p. 289, follows from the
    independently specified polynomial law. *)
Lemma structure_enlarged_aperture_inverse_equation (R:realType) k (s u:R):
  (0<k)%N ->0<s ->is_structure_enlarged_aperture k s u ->
  (u^-1)^+2-1=((s^-1)^+2-1)/(k%:R).
Proof.
move=>hk hs [/andP [hu hu1] hEq].
have hK:0<(k%:R:R) by rewrite ltr0n.
have hs2:0<s^+2 by rewrite exprn_gt0.
have hUSq:u^+2=(k%:R*s^+2)/(1+(k%:R-1)*s^+2).
  have hDen:0<1+(k%:R-1)*s^+2.
    have hK1:(1:R)<=k%:R by rewrite ler1n.
    nra.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - by rewrite (ler_pdivlMr _ _ hDen) hEq.
  - by rewrite (ler_pdivrMr _ _ hDen) hEq.
rewrite !exprVn hUSq invf_div.
field; by rewrite ?mulf_eq0 ?(gt_eqF hK) ?(gt_eqF hs) ?expf_eq0.
Qed.
