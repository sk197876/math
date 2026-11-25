(** Federer (1969), 3.3.4, pp. 289–290:
    the actual extension of an orthogonal
    active-space map is orthogonal on the
    whole original inner-product space. Use
    only the independent extension laws and
    adjoint pairing, never a private formula. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom Bilinear InnerProductUP InnerProductLaws
  OrthogonalMaps InjectionExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [injection_extension_orthogonal]: the
    subgroup acts orthogonally on the actual
    active space and fixes its orthogonal
    complement, Federer 3.3.4, pp. 289–290.
    The supplied q is the actual adjoint
    retraction, so the two subspaces are
    orthogonal and cover the original space. *)
Theorem injection_extension_orthogonal (R:realFieldType) (U V:lmodType R)
    (B:U->U->R) (C:V->V->R) (hB:is_inner_product B) (hC:is_inner_product C)
    (w:Hom U V) (q:Hom V U) (h:Hom U U) (H:Hom V V):
  cancel w q ->(forall u x,B u (q x)=C (w u) x) ->
  is_orthogonal_map B B (hom_as_linear h) ->
  is_injection_extension w q h H ->is_orthogonal_map C C (hom_as_linear H).
Proof.
move=>hCancel hAdjoint hOrthogonal hExtension x y.
have hNormal z:q (z-w (q z))=0 by rewrite (linearB (hom_as_linear q)) !hom_as_linearE hCancel subrr.
have hCross u z:C (w u) (z-w (q z))=0.
  by rewrite -hAdjoint hNormal (bil0r (inner_bilinear hB)).
have hPair u v:C (x-w (q x)+w u) (y-w (q y)+w v)=
    C (x-w (q x)) (y-w (q y))+B u v.
  rewrite (bilDl (inner_bilinear hC)).
  rewrite (bilDr (inner_bilinear hC) (x-w (q x)) (y-w (q y)) (w v))
    (bilDr (inner_bilinear hC) (w u) (y-w (q y)) (w v)).
  rewrite [C (x-w (q x)) (w v)](inner_symmetric hC) !hCross.
  by rewrite -hAdjoint hCancel addr0 add0r.
have hO u v:B (h u) (h v)=B u v:=hOrthogonal u v.
change (C (H x) (H y)=C x y).
rewrite (injection_extension_decomposition hCancel hExtension)
  (injection_extension_decomposition hCancel hExtension) hPair hO.
have hOriginal:=hPair (q x) (q y).
by rewrite !subrK in hOriginal; exact:esym hOriginal.
Qed.
