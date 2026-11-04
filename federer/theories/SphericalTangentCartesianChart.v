(** Federer (1969), 3.2.48, p. 285: the direct-sum
    rows of the actual differential diagram are isometric
    Cartesian tangent coordinates. Independent Gram/evaluation laws
    precede the local existence proof. No chart or inverse
    is globally selected, and no Jacobian is a premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets ring.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerProductLaws
  InnerProductRestriction InnerNorm EuclideanHomInnerCharts OrthogonalMaps
  EuclideanGramDifferentialAlgebra SphericalHorizontalLift SphericalHorizontalLiftLinear
  SphericalTangentOrthogonalSplit EuclideanStiefelHalfNormalization ProductInner LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_tangent_cartesian_chart]: supporting
    the actual orthogonal direct sums in 3.2.48,
    p. 285. K has the vertical Gram-and-zero-evaluation
    laws, S lies in the sphere tangent hyperplane, and
    T has the original preimage tangent equations. These
    laws are discharged by the preceding geometric results.
    The normalized lift gives an isometric bijection, with
    an inverse used only through its proved linear laws. *)
Theorem spherical_tangent_cartesian_chart (R:realType) N (c:R_n R N)
    (K:subspace (Hom (R_n R N) (R_n R N)))
    (S:subspace (R_n R N)) (T:subspace (Hom (R_n R N) (R_n R N))):
  inner_norm (@euclidean_inner_productP R N) c= 1 ->
  (forall w,K w <->euclidean_gram_differential (hom_of_linear (linear_id (R_n R N))) w=0 /\w c=0) ->
  (forall v,S v ->euclidean_inner_product c v=0) ->
  (forall w,T w <->euclidean_gram_differential (hom_of_linear (linear_id (R_n R N))) w=0 /\S (w c)) ->
  let P:lmodType R:=[the lmodType R of (subspace_space K*subspace_space S)%type] in
  exists (i:Hom P (subspace_space T)) (j:Hom (subspace_space T) P),
    cancel i j /\cancel j i /\
    is_orthogonal_map
      (product_inner (restricted_inner_productP (@euclidean_hom_inner_productP R N N) K)
        (restricted_inner_productP (@euclidean_inner_productP R N) S))
      (@restricted_inner_product R _ (@euclidean_hom_inner_product R N N) T) (hom_as_linear i) /\
    forall x,subspace_val (i x)=subspace_val x.1+
      (Num.sqrt (2:R))^-1*:spherical_horizontal_lift (hom_of_linear (linear_id (R_n R N))) c (subspace_val x.2).
Proof.
move=>hc hK hS hT P.
pose V:=R_n R N.
pose H:=Hom V V.
pose idV:Hom V V:=hom_of_linear (linear_id V).
pose s:=(Num.sqrt (2:R))^-1.
pose L:=spherical_horizontal_lift idV c.
have hId:is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear idV) by move=>x y.
have hUnit:euclidean_inner_product c c= 1.
  by rewrite -(inner_norm_sqr (@euclidean_inner_productP R N)) hc expr1n.
have hLLinear:linear L:=spherical_horizontal_lift_linear idV c.
have hEval v (hv:S v):L v c=v.
  exact (@spherical_horizontal_lift_evaluation R N idV c v hUnit (hS v hv)).
have hMember (x:P):T (subspace_val x.1+s*:L (subspace_val x.2)).
  have [hzG hzC]:=(hK _).1 (subspace_valP x.1).
  apply:(hT _).2; split.
  - rewrite linearD linearZ.
    change (euclidean_gram_differential idV (subspace_val x.1)+
      s*:euclidean_gram_differential idV (L (subspace_val x.2))=0).
    by rewrite hzG
      (@spherical_horizontal_lift_tangent R N idV c (subspace_val x.2) hId) scaler0 addr0.
  - change (S (subspace_val x.1 c+s*:(L (subspace_val x.2) c))).
    rewrite hzC (hEval _ (subspace_valP x.2)) add0r.
    exact (subspace_scale s (subspace_valP x.2)).
pose map0:=fun x:P=>@subspace_lift R H T (subspace_val x.1+s*:L (subspace_val x.2)) (hMember x).
have hMapLinear:linear map0.
  move=>a x y; apply:subspace_val_injective.
  change (a*:subspace_val x.1+subspace_val y.1+s*:L (a*:subspace_val x.2+subspace_val y.2)=
    a*:(subspace_val x.1+s*:L (subspace_val x.2))+(subspace_val y.1+s*:L (subspace_val y.2))).
  rewrite (hLLinear a (subspace_val x.2) (subspace_val y.2)) !scalerDr !scalerA.
  by rewrite [s*a]mulrC addrACA.
pose i:Hom P (subspace_space T):=@HomMap R P (subspace_space T) map0 (introT (asboolP _) hMapLinear).
pose hKInner:=restricted_inner_productP (@euclidean_hom_inner_productP R N N) K.
pose hSInner:=restricted_inner_productP (@euclidean_inner_productP R N) S.
pose hTInner:=restricted_inner_productP (@euclidean_hom_inner_productP R N N) T.
pose hPInner:=product_inner_productP hKInner hSInner.
have [hs hScale]:=euclidean_stiefel_half_normalization R.
have hPair v u (hu:S u):euclidean_hom_inner_product (L v) (L u)= 2*euclidean_inner_product v u.
  rewrite (@spherical_horizontal_lift_pairing R N idV (L u) c v hId
    (@spherical_horizontal_lift_tangent R N idV c u hId)) (hEval u hu).
  reflexivity.
have hCross v z (hz:K z):euclidean_hom_inner_product (L v) z=0.
  have [hzG hzC]:=(hK z).1 hz.
  by rewrite (@spherical_horizontal_lift_pairing R N idV z c v hId hzG) hzC
    (bil0r (inner_bilinear (@euclidean_inner_productP R N))) mulr0.
have hOrthogonal:is_orthogonal_map (product_inner hKInner hSInner)
    (@restricted_inner_product R H (@euclidean_hom_inner_product R N N) T) (hom_as_linear i).
  move=>x y.
  change (euclidean_hom_inner_product (subspace_val x.1+s*:L (subspace_val x.2))
    (subspace_val y.1+s*:L (subspace_val y.2))=
    product_inner hKInner hSInner x y).
  rewrite product_innerE
    (bilDl (inner_bilinear (@euclidean_hom_inner_productP R N N)))
    !(bilDr (inner_bilinear (@euclidean_hom_inner_productP R N N)))
    !(bilZl (inner_bilinear (@euclidean_hom_inner_productP R N N)))
    !(bilZr (inner_bilinear (@euclidean_hom_inner_productP R N N))).
  rewrite (hCross _ _ (subspace_valP y.1))
    (inner_symmetric (@euclidean_hom_inner_productP R N N) (subspace_val x.1) (L (subspace_val y.2)))
    (hCross _ _ (subspace_valP x.1)) (hPair _ _ (subspace_valP y.2)) !scaler0 !addr0 ?add0r.
  change (euclidean_hom_inner_product (subspace_val x.1) (subspace_val y.1)+
    s*(s*(2*euclidean_inner_product (subspace_val x.2) (subspace_val y.2)))=
    euclidean_hom_inner_product (subspace_val x.1) (subspace_val y.1)+
    euclidean_inner_product (subspace_val x.2) (subspace_val y.2)).
  have hFactor:s*(s*(2*euclidean_inner_product (subspace_val x.2) (subspace_val y.2)))=
    (2*s*s)*euclidean_inner_product (subspace_val x.2) (subspace_val y.2) by ring.
  by rewrite hFactor hScale mul1r.
have hInjective:injective (hom_as_linear i).
  exact (orthogonal_map_injective hPInner hTInner hOrthogonal).
have hSurjective:forall w:subspace_space T,exists x:P,i x=w.
  move=>w; have [hwG hwS]:=(hT _).1 (subspace_valP w).
  have [z [hzG [hzC [hSum hOrth]]]]:=@spherical_gram_tangent_orthogonal_split R N idV (subspace_val w) c hId hc hwG.
  have hz:K z:=(hK z).2 (conj hzG hzC).
  have hu:S (Num.sqrt (2:R)*:(subspace_val w c)):=subspace_scale _ hwS.
  exists (@subspace_lift R H K z hz,@subspace_lift R V S _ hu).
  apply:subspace_val_injective.
  change (z+s*:L (Num.sqrt (2:R)*:(subspace_val w c))=subspace_val w).
  rewrite (linZ hLLinear) scalerA /s mulVf ?scale1r.
  - exact (esym hSum).
  - by rewrite gt_eqF // sqrtr_gt0 ltr0n.
pose j:Hom (subspace_space T) P:=hom_of_linear
  (GRing.Linear.clone _ _ _ _ (@linear_inverse R P (subspace_space T) (hom_as_linear i) hInjective hSurjective) _).
exists i,j; split.
- exact (@linear_inverseKV R P (subspace_space T) (hom_as_linear i) hInjective hSurjective).
- split.
  + exact (@linear_inverseK R P (subspace_space T) (hom_as_linear i) hInjective hSurjective).
  + split; first exact hOrthogonal.
    by move=>x.
Qed.
