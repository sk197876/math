(** Federer (1969), 3.2.48, p. 286: transform the starred tangent
    word by the actual orthogonal isotropy action. Supporting naturality
    from 1.6.5, pp. 25–26, and 1.7.8, p. 34. The norm removes only
    the proved unit orientation scalar; no sign choice is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Bilinear InnerProductUP InnerExterior InnerExteriorNaturality
  ExteriorGrading ExteriorMaps ExteriorNorm ExteriorNormNaturality ExteriorHomogeneousProducts
  OrthogonalMaps LinearBasis TopExteriorNorm HodgeMaps DualityMaps InteriorNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [hodge_vector_orthogonal_natural]: the actual star
    intertwines the isometry when the top volume is also transported,
    supporting the isotropy calculation in 3.2.48, p. 286. Naturality
    is proved from the public contraction and polarity laws. *)
Theorem hodge_vector_orthogonal_natural (R:realFieldType) (h2:(1+1:R)!=0)
    (V W:lmodType R) B C (hV:@is_inner_product R V B) (hW:@is_inner_product R W C)
    (f:{linear V->W}) n (E:exterior_power V n) p (hp:(p<=n)%N) (x:exterior_power V p):
  is_orthogonal_map B C f ->
  exterior_power_map f (n-p) (hodge_vector h2 hV E hp x)=
    hodge_vector h2 hW (exterior_power_map f n E) hp (exterior_power_map f p x).
Proof.
move=>hf.
have hPull:=@inner_exterior_form_orthogonal_natural R h2 V W B C hV hW f hf p x.
rewrite /hodge_vector /D_upper -{1}hPull.
exact (@left_interior_natural R h2 V W f p n hp E (inner_exterior_form h2 hW (exterior_power_map f p x))).
Qed.

(** Source for [hodge_wedge_orthogonal_transport]: the actual norm
    identity used before applying 2.7.16(6) in 3.2.48, p. 286.
    The local top-volume factor has absolute value one by orthogonality;
    it is removed only inside the exterior norm. Zero and top degrees
    and both zero-dimensional orientations are retained. *)
Theorem hodge_wedge_orthogonal_transport (R:realType) (h2:(1+1:R)!=0)
    (V:lmodType R) B (hV:@is_inner_product R V B) n (b:'I_n->V) (hb:is_basis b)
    (E:exterior_power V n) (hE:exterior_norm h2 hV E= 1)
    (f:{linear V->V}) p (hp:(p<=n)%N) (x:exterior_power V p) r (z:exterior_power V r):
  is_orthogonal_map B B f ->
  exterior_norm h2 hV (exterior_product z (hodge_vector h2 hV E hp (exterior_power_map f p x)))=
  exterior_norm h2 hV (exterior_product z (exterior_power_map f (n-p) (hodge_vector h2 hV E hp x))).
Proof.
move=>hf.
have hNonzero:E!=0.
  apply/eqP=>hZero; move:hE; rewrite hZero exterior_norm_zero=>/eqP.
  by rewrite eq_sym oner_eq0.
have [c hTop]:=@nonzero_top_vector_spans R h2 V n b hb E hNonzero (exterior_power_map f n E).
have hAbs:`|c|= 1.
  have hUnit:=@exterior_norm_orthogonal_natural R h2 V V B B hV hV f hf n E.
  by rewrite hTop exterior_norm_scale hE mulr1 in hUnit.
rewrite (@hodge_vector_orthogonal_natural R h2 V V B B hV hV f n E p hp x hf)
  hTop hodge_vector_volume_scale (bilZr (@exterior_product_bilinear R V r (n-p)))
  exterior_norm_scale hAbs mul1r.
reflexivity.
Qed.
