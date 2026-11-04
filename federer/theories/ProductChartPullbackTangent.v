(** Federer (1969), 3.2.47, p. 283: the tangent
    of Phi inverse(E) is the inverse image of Tan(E)
    inside the actual group tangent. This supporting chart
    lemma proves the assertion from actual local retractions,
    the chain rule and the two printed inverse identities. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP InnerProductUP InnerNorm HilbertFormCompactness ProductInner
  RealNormUP NormDifferentialUP NormDifferentialLocal NormDifferentialChain
  NormDifferentialLinear NormLinearDomainLaws ProductInnerDifferential
  TangentConeUP TangentConeBasic TangentOpenDomain TangentDifferentialImage RetractionTangentIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PullbackTangent.
Variable R:realType.
Variables X V W:lmodType R.
Variables (BX:X->X->R) (BV:V->V->R) (BW:W->W->R).
Hypotheses (hX:@is_inner_product R X BX)
  (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW).
Local Notation NX:=(inner_norm hX).
Local Notation NV:=(inner_norm hV).
Local Notation NW:=(inner_norm hW).
Local Notation hNX:=(inner_norm_real_norm hX).
Local Notation hNV:=(inner_norm_real_norm hV).
Local Notation hNW:=(inner_norm_real_norm hW).
Local Notation NP:=(inner_norm (product_inner_productP hV hW)).
Local Notation hNP:=(inner_norm_real_norm (product_inner_productP hV hW)).
Local Notation P:=[the lmodType R of (V*W)%type].
Variables (O S D:set X) (E TE:set V) (I TI:set W) (B:set P).
Variables (p:X->V) (h:X->W) (j:P->X) (re:V->V) (ri:W->W).
Variable a:X.
Variables (L:Hom X V) (M:Hom X W) (J:Hom P X) (LE:Hom V V) (LI:Hom W W).
Hypothesis hS:forall x,S x <->O x /\E (p x).
Hypotheses (ha:S a) (haD:D a).
Hypothesis hp:has_norm_differential NX NV D p a L.
Hypothesis hh:has_norm_differential NX NW D h a M.
Hypothesis hj:has_norm_differential NP NX B j (p a,h a) J.
Hypothesis hre:has_norm_differential NV NV TE re (p a) LE.
Hypothesis hri:has_norm_differential NW NW TI ri (h a) LI.
Hypothesis hH:forall x,O x ->D x ->I (h x).
Hypothesis hPair:forall x,D x ->B (p x,h x).
Hypothesis hInverse:forall x,O x ->D x ->j (p x,h x)=x.
Hypothesis hProduct:forall y z,E y ->I z ->B (y,z) /\S (j (y,z)).
Hypothesis hRE:forall y,TE y ->E (re y).
Hypothesis hRI:forall z,TI z ->I (ri z).
Hypothesis hFixE:forall y,E y ->TE y ->re y=y.
Hypothesis hFixI:forall z,I z ->TI z ->ri z=z.

(** Source for [product_chart_pullback_tangent]: the actual
    tangent inverse-image identity underlying the last display
    in 3.2.47, p. 283. Reverse inclusion is
    proved by differentiating a local retraction built from
    the printed product chart; no tangent equality is assumed. *)
Theorem product_chart_pullback_tangent:
  norm_tangent_cone NX S a=
    [set w|norm_tangent_cone NX O a w /\norm_tangent_cone NV E (p a) (L w)].
Proof.
have [haO haE]:=(hS a).1 ha.
have haI:I (h a):=@hH a haO haD.
have haTE:TE (p a):=norm_domain_interior_member hNV (norm_differential_interior hre).
have haTI:TI (h a):=norm_domain_interior_member hNW (norm_differential_interior hri).
have hrea:re (p a)=p a:=@hFixE (p a) haE haTE.
have hria:ri (h a)=h a:=@hFixI (h a) haI haTI.
pose A:=fun x=> (D x /\TE (p x)) /\(D x /\TI (h x)).
have hA:norm_domain_interior NX A a.
  exact (@norm_domain_intersection_interior R X NX _ _ a
    (@norm_differential_composite_interior R X V NX NV hNV D TE p a L hp
      (norm_differential_interior hre))
    (@norm_differential_composite_interior R X W NX NW hNW D TI h a M hh
      (norm_differential_interior hri))).
have hpA:=@norm_differential_restrict R X V NX NV D A p a L (fun x hx=>hx.1.1) hA hp.
have hhA:=@norm_differential_restrict R X W NX NW D A h a M (fun x hx=>hx.1.1) hA hh.
have hreP:=@norm_differential_compose_on R X V V NX NV NV hNX hNV hNV A TE p re a L LE
  (fun x hx=>hx.1.2) hpA hre.
have hriH:=@norm_differential_compose_on R X W W NX NW NW hNX hNW hNW A TI h ri a M LI
  (fun x hx=>hx.2.2) hhA hri.
have hQ:=@norm_differential_inner_pair R X V W NX hNX BV BW hV hW A
  (fun x=>re (p x)) (fun x=>ri (h x)) a (hom_comp LE L) (hom_comp LI M) hreP hriH.
have hJAt:has_norm_differential NP NX B j (re (p a),ri (h a)) J.
  by rewrite hrea hria.
have hQMap x (hx:A x):B (re (p x),ri (h x)).
  exact (@hProduct _ _ (@hRE _ hx.1.2) (@hRI _ hx.2.2)).1.
pose f:=fun x=>j (re (p x),ri (h x)).
pose DF:=hom_comp J (product_pair_hom (hom_comp LE L) (hom_comp LI M)).
have hf:has_norm_differential NX NX A f a DF.
  exact (@norm_differential_compose_on R X P X NX NP NX hNX hNP hNX A B
    (fun x=>(re (p x),ri (h x))) j a _ J hQMap hQ hJAt).
have hfa:f a=a.
  rewrite /f hrea hria; exact (@hInverse a haO haD).
have hfS x (hx:A x):S (f x).
  exact (@hProduct _ _ (@hRE _ hx.1.2) (@hRI _ hx.2.2)).2.
have hQ0:=@norm_differential_inner_pair R X V W NX hNX BV BW hV hW D p h a L M hp hh.
pose f0:=fun x=>j (p x,h x).
pose DF0:=hom_comp J (product_pair_hom L M).
have hf0:has_norm_differential NX NX D f0 a DF0.
  exact (@norm_differential_compose_on R X P X NX NP NX hNX hNP hNX D B
    (fun x=>(p x,h x)) j a _ J hPair hQ0 hj).
apply/seteqP; split=>w.
- move=>hw; split.
  + exact (@norm_tangent_mono R X NX S O a (fun x hx=>((hS x).1 hx).1) w hw).
  + have hi:=@norm_differential_tangent_image R X V NX NV hNX hNV D S p a L hp w hw.
    apply:(@norm_tangent_mono R V NV (p @` (S `&` D)) E (p a) _ (L w) hi).
    move=>y [x [hx _] <-]; exact ((hS x).1 hx).2.
- move=>[hwO hwE].
  have hi:=@norm_differential_tangent_image R X W NX NW hNX hNW D O h a M hh w hwO.
  have hwI:norm_tangent_cone NW I (h a) (M w).
    apply:(@norm_tangent_mono R W NW (h @` (O `&` D)) I (h a) _ (M w) hi).
    move=>z [x [hx hxD] <-]; exact (@hH x hx hxD).
  have hLE:LE (L w)=L w.
    exact (@norm_retraction_differential_tangent R V NV hNV E TE re (p a) LE
      haE hre hFixE (L w) hwE).
  have hLI:LI (M w)=M w.
    exact (@norm_retraction_differential_tangent R W NW hNW I TI ri (h a) LI
      haI hri hFixI (M w) hwI).
  have hDF0:DF0 w=w.
    exact (@norm_retraction_differential_tangent R X NX hNX O D f0 a DF0
      haO hf0 hInverse w hwO).
  have hDF:DF w=w.
    change (J (product_pair_hom (hom_comp LE L) (hom_comp LI M) w)=w).
    rewrite product_pair_homE.
    change (J (LE (L w),LI (M w))=w).
    rewrite hLE hLI.
    have hValue:DF0 w=J (L w,M w).
      change (J (product_pair_hom L M w)=J (L w,M w)).
      by rewrite product_pair_homE.
    by rewrite -hValue.
  have hwA:norm_tangent_cone NX A a w.
    by rewrite (norm_tangent_open_domain hNX hA).
  have hImage:=@norm_differential_tangent_image R X X NX NX hNX hNX A A f a DF hf w hwA.
  have hResult:norm_tangent_cone NX S (f a) (DF w).
    apply:(@norm_tangent_mono R X NX (f @` (A `&` A)) S (f a) _ (DF w) hImage).
    move=>x [y [hy _] <-]; exact (@hfS y hy).
  by rewrite hfa hDF in hResult.
Qed.
End PullbackTangent.
