(** Federer (1969), 3.3.4, p. 290:
    an orthogonal map fixing the actual
    orthogonal complement preserves the active
    space. This derives the subgroup
    identification from original inner-product laws. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom Bilinear BilinearNegation InnerProductUP InnerProductLaws
  OrthogonalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [injection_fixed_normal_range]: the
    actual K fixing the complementary
    directions restricts to an orthogonal
    operator on X, Federer 3.3.4,
    p. 290. The projected residual is
    fixed and orthogonal to the active
    vector; orthogonality then forces that
    residual to vanish. No selected frame
    completion or private extension formula is used. *)
Theorem injection_fixed_normal_range (R:realFieldType) (U V:lmodType R)
    (B:U->U->R) (C:V->V->R) (hB:is_inner_product B) (hC:is_inner_product C)
    (w:Hom U V) (q:Hom V U) (K:Hom V V):
  cancel w q ->(forall u x,B u (q x)=C (w u) x) ->
  is_orthogonal_map C C (hom_as_linear K) ->
  (forall x,q x=0 ->K x=x) ->forall u,K (w u)=w (q (K (w u))).
Proof.
move=>hCancel hAdjoint hK hFixed u.
pose x:=K (w u).
pose r:=x-w (q x).
have hNormal:q r=0 by rewrite /r (linearB (hom_as_linear q)) !hom_as_linearE hCancel subrr.
have hCross v:C (w v) r=0 by rewrite -hAdjoint hNormal (bil0r (inner_bilinear hB)).
have hX:C x r=0.
  have hOrthogonal:=hK (w u) r.
  change (C (K (w u)) (K r)=C (w u) r) in hOrthogonal.
  by rewrite (hFixed r hNormal) hCross in hOrthogonal.
have hSquare:C r r=0.
  by rewrite /r (bilBl (inner_bilinear hC)) hX hCross subrr.
have hZero:r=0 by apply/eqP; rewrite -(inner_self_eq0 hC) hSquare eqxx.
move/eqP:hZero; by rewrite /r subr_eq0=>/eqP.
Qed.
