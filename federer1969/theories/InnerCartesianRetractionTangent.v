(** Federer (1969), 3.2.48, p. 285: the source tangent is the
    Cartesian product of the two actual manifold tangents. Supporting
    proof from the local retractions of 3.1.19, p. 231; arbitrary
    Cartesian subsets alone need not have this tangent product law. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP InnerProductUP InnerNorm ProductInner
  ProductInnerNormBounds ProductInnerDifferential HilbertFormCompactness RealNormUP NormDifferentialUP
  NormDifferentialLinear NormLinearDomainLaws NormOpenDomainLaws TangentConeUP
  TangentConeBasic TangentOpenDomain TangentDifferentialImage RetractionTangentIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_cartesian_retraction_tangent]: the top left
    tangent row in 3.2.48, p. 285. Actual local retractions provide
    the reverse inclusion, rather than an invalid tangent-product rule
    for arbitrary subsets. Both zero-dimensional factors are retained. *)
Theorem inner_cartesian_retraction_tangent (R:realType) (V W:lmodType R)
    BV BW (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    (M A:set V) (N B:set W) (f:V->V) (g:W->W) (a:V) (b:W)
    (D:Hom V V) (E:Hom W W):
  M a ->N b ->
  has_norm_differential (inner_norm hV) (inner_norm hV) A f a D ->
  has_norm_differential (inner_norm hW) (inner_norm hW) B g b E ->
  (forall x,A x ->M (f x)) ->(forall y,B y ->N (g y)) ->
  (forall x,M x ->A x ->f x=x) ->(forall y,N y ->B y ->g y=y) ->
  norm_tangent_cone (inner_norm (product_inner_productP hV hW))
    [set z:V*W|M z.1 /\N z.2] (a,b)=
    [set z:V*W|norm_tangent_cone (inner_norm hV) M a z.1 /\
      norm_tangent_cone (inner_norm hW) N b z.2].
Proof.
move=>ha hb hf hg hfM hgN hfFix hgFix.
pose P:lmodType R:=[the lmodType R of (V*W)%type].
pose hP:=product_inner_productP hV hW.
pose p:=@product_first_projection_hom R V W.
pose q:=@product_second_projection_hom R V W.
have hp:norm_bounded_linear (inner_norm hP) (inner_norm hV) p.
  exists 1; split; first exact:ler01.
  by move=>z; rewrite mul1r; exact (product_inner_first_norm_bound hV hW z).
have hq:norm_bounded_linear (inner_norm hP) (inner_norm hW) q.
  exists 1; split; first exact:ler01.
  by move=>z; rewrite mul1r; exact (product_inner_second_norm_bound hV hW z).
pose C:=fun z:P=>A (p z) /\B (q z).
have hA:=norm_differential_interior hf.
have hB:=norm_differential_interior hg.
have hC:norm_domain_interior (inner_norm hP) C (a,b).
  apply:norm_domain_intersection_interior.
  - exact (norm_bounded_linear_preimage_interior (inner_norm_real_norm hP) hp hA).
  - exact (norm_bounded_linear_preimage_interior (inner_norm_real_norm hP) hq hB).
have hDp:=@norm_differential_linear R P V _ _ (inner_norm_real_norm hP)
  (inner_norm_real_norm hV) C (a,b) p hC hp.
have hDq:=@norm_differential_linear R P W _ _ (inner_norm_real_norm hP)
  (inner_norm_real_norm hW) C (a,b) q hC hq.
have hDf:=@norm_differential_compose_on R P V V _ _ _ (inner_norm_real_norm hP)
  (inner_norm_real_norm hV) (inner_norm_real_norm hV) C A p f (a,b) p D
  (fun z hz=>hz.1) hDp hf.
have hDg:=@norm_differential_compose_on R P W W _ _ _ (inner_norm_real_norm hP)
  (inner_norm_real_norm hW) (inner_norm_real_norm hW) C B q g (a,b) q E
  (fun z hz=>hz.2) hDq hg.
have hPair:=@norm_differential_inner_pair R P V W _ (inner_norm_real_norm hP) BV BW hV hW C
  (fun z=>f (p z)) (fun z=>g (q z)) (a,b) (hom_comp D p) (hom_comp E q) hDf hDg.
have hfa:f a=a:=hfFix a ha (norm_domain_interior_member (inner_norm_real_norm hV) hA).
have hgb:g b=b:=hgFix b hb (norm_domain_interior_member (inner_norm_real_norm hW) hB).
apply/seteqP; split.
- move=>[u v] hTan; split.
  + have hImage:=@norm_differential_tangent_image R P V _ _ (inner_norm_real_norm hP)
      (inner_norm_real_norm hV) C [set z:V*W|M z.1 /\N z.2] p (a,b) p hDp (u,v) hTan.
    apply:(@norm_tangent_mono R V (inner_norm hV) _ M a _ u hImage).
    move=>x [z [[hzM hzN] hzC] <-]; exact hzM.
  + have hImage:=@norm_differential_tangent_image R P W _ _ (inner_norm_real_norm hP)
      (inner_norm_real_norm hW) C [set z:V*W|M z.1 /\N z.2] q (a,b) q hDq (u,v) hTan.
    apply:(@norm_tangent_mono R W (inner_norm hW) _ N b _ v hImage).
    move=>x [z [[hzM hzN] hzC] <-]; exact hzN.
- move=>[u v] [hu hv].
  have hDu:D u=u:=norm_retraction_differential_tangent (inner_norm_real_norm hV) ha hf hfFix hu.
  have hEv:E v=v:=norm_retraction_differential_tangent (inner_norm_real_norm hW) hb hg hgFix hv.
  have hOpen:norm_tangent_cone (inner_norm hP) C (a,b) (u,v).
    by rewrite (norm_tangent_open_domain (inner_norm_real_norm hP) hC).
  have hImage:=@norm_differential_tangent_image R P P _ _ (inner_norm_real_norm hP)
    (inner_norm_real_norm hP) C C (fun z=>(f (p z),g (q z))) (a,b)
    (product_pair_hom (hom_comp D p) (hom_comp E q)) hPair (u,v) hOpen.
  rewrite product_pair_homE in hImage.
  change (norm_tangent_cone (inner_norm hP)
    ((fun z=>(f (p z),g (q z))) @` (C `&` C)) (f a,g b) (D u,E v)) in hImage.
  rewrite hfa hgb hDu hEv in hImage.
  apply:(@norm_tangent_mono R P (inner_norm hP) _ [set z:V*W|M z.1 /\N z.2]
    (a,b) _ (u,v) hImage).
  move=>z [w [hw _] <-]; split; [exact (hfM _ hw.1)|exact (hgN _ hw.2)].
Qed.
