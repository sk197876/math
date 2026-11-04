(** Federer (1969), 3.2.48, p. 285: actual isometric tangent
    coordinates after left translation and a transverse orthogonal frame.
    Independent Gram and coordinate laws precede the local inverse witness. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets ring.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerProductLaws
  InnerProductRestriction InnerNorm EuclideanHomInnerCharts OrthogonalMaps
  EuclideanGramDifferentialAlgebra SphericalHorizontalLift SphericalHorizontalLiftLinear
  SphericalHorizontalSpace SphericalTangentOrthogonalSplit EuclideanStiefelHalfNormalization ProductInner LinearBasis
  HomCompositionDeterminant HilbertFormCompactness EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  SphericalTangentCoordinates SphericalCoordinateIsotropy OrthogonalKinematicIsometries.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_translated_cartesian_chart]: the isometric
    source tangent rows in 3.2.48, p. 285. The exact forward map is
    left translation of the vertical vector plus the normalized horizontal
    lift of the transverse vector. The inverse is local and used through
    its linear cancellation laws; no chart or Jacobian is assumed. *)
Theorem spherical_translated_cartesian_chart (R:realType) d (c:R_n R (1+d))
    (g Q:Hom (R_n R (1+d)) (R_n R (1+d)))
    (K:subspace (Hom (R_n R (1+d)) (R_n R (1+d))))
    (S:subspace (R_n R d)) (T:subspace (Hom (R_n R (1+d)) (R_n R (1+d)))):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear g) ->
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  Q (spherical_coordinate_pole R d)=c ->
  (forall w,K w <->euclidean_gram_differential (hom_of_linear (linear_id (R_n R (1+d)))) w=0 /\w c=0) ->
  (forall w,T w <->
    euclidean_gram_differential (hom_of_linear (linear_id (R_n R (1+d))))
      (hom_comp (euclidean_rectangular_adjoint g) w)=0 /\
    S (spherical_transverse_coordinates Q ((hom_comp (euclidean_rectangular_adjoint g) w) c))) ->
  let P:lmodType R:=[the lmodType R of (subspace_space K*subspace_space S)%type] in
  exists (i:Hom P (subspace_space T)) (j:Hom (subspace_space T) P),
    cancel i j /\cancel j i /\
    is_orthogonal_map
      (product_inner (restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) K)
        (restricted_inner_productP (@euclidean_inner_productP R d) S))
      (@restricted_inner_product R _ (@euclidean_hom_inner_product R (1+d) (1+d)) T) (hom_as_linear i) /\
    forall x,subspace_val (i x)=hom_comp g (subspace_val x.1+
      (Num.sqrt (2:R))^-1*:spherical_horizontal_lift (hom_of_linear (linear_id (R_n R (1+d)))) c
        (spherical_transverse_embedding Q (subspace_val x.2))).
Proof.
move=>hc hg hQ hQc hK hT P.
pose V:=R_n R (1+d).
pose H:=Hom V V.
pose idV:Hom V V:=hom_of_linear (linear_id V).
pose s:=(Num.sqrt (2:R))^-1.
pose J:=spherical_transverse_embedding Q.
pose C:=spherical_transverse_coordinates Q.
pose L:=fun v:R_n R d=>spherical_horizontal_lift idV c (J v).
pose G:Hom H H:=hom_of_linear (@hom_left_composition R V V g).
have hCancel f:hom_comp (euclidean_rectangular_adjoint g) (G f)=f.
  by apply:hom_ext=>x; exact (euclidean_orthogonal_adjoint_cancel hg (f x)).
have hCancelReverse f:G (hom_comp (euclidean_rectangular_adjoint g) f)=f.
  by apply:hom_ext=>x; exact (euclidean_orthogonal_adjoint_cancel_reverse hg (f x)).
have hLeftPair f f':euclidean_hom_inner_product (G f) (G f')=euclidean_hom_inner_product f f'.
  have hRight z:hom_comp z idV=z by apply:hom_ext=>x.
  have hId:is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear idV) by move=>x y.
  have h:=@orthogonal_kinematic_sandwich_pairing R (1+d) idV g f f' hId hg.
  by rewrite !hRight in h.
have hJ:=spherical_transverse_embedding_orthogonal hQ.
have hJC:=spherical_transverse_coordinatesK hQ.
have hPerp v:euclidean_inner_product c (J v)=0.
  by rewrite -hQc; exact (spherical_transverse_embedding_perpendicular hQ v).
have hId:is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear idV) by move=>x y.
have hUnit:euclidean_inner_product c c= 1.
  by rewrite -(inner_norm_sqr (@euclidean_inner_productP R (1+d))) hc expr1n.
have hLLinear:linear L.
  move=>a x y; rewrite /L linearD linearZ.
  change (spherical_horizontal_lift idV c (a*:J x+J y)=
    a*:spherical_horizontal_lift idV c (J x)+spherical_horizontal_lift idV c (J y)).
  exact (spherical_horizontal_lift_linear idV c a (J x) (J y)).
have hEval v:L v c=J v.
  exact (@spherical_horizontal_lift_evaluation R (1+d) idV c (J v) hUnit (hPerp v)).
have hMember (x:P):T (G (subspace_val x.1+s*:L (subspace_val x.2))).
  have [hzG hzC]:=(hK _).1 (subspace_valP x.1).
  apply:(hT _).2; rewrite hCancel; split.
  - rewrite linearD linearZ.
    change (euclidean_gram_differential idV (subspace_val x.1)+
      s*:euclidean_gram_differential idV (L (subspace_val x.2))=0).
    by rewrite hzG
      (@spherical_horizontal_lift_tangent R (1+d) idV c (J (subspace_val x.2)) hId) scaler0 addr0.
  - change (S (C (subspace_val x.1 c+s*:(L (subspace_val x.2) c)))).
    rewrite hzC hEval add0r (linZ (hom_linear C)) hJC.
    exact (subspace_scale s (subspace_valP x.2)).
pose map0:=fun x:P=>@subspace_lift R H T (G (subspace_val x.1+s*:L (subspace_val x.2))) (hMember x).
have hMapLinear:linear map0.
  move=>a x y; apply:subspace_val_injective.
  change (G (a*:subspace_val x.1+subspace_val y.1+s*:L (a*:subspace_val x.2+subspace_val y.2))=
    a*:G (subspace_val x.1+s*:L (subspace_val x.2))+G (subspace_val y.1+s*:L (subspace_val y.2))).
  rewrite -(hom_linear G a (subspace_val x.1+s*:L (subspace_val x.2))
    (subspace_val y.1+s*:L (subspace_val y.2))).
  congr (G _).
  rewrite (hLLinear a (subspace_val x.2) (subspace_val y.2)) !scalerDr !scalerA.
  by rewrite [s*a]mulrC addrACA.
pose i:Hom P (subspace_space T):=@HomMap R P (subspace_space T) map0 (introT (asboolP _) hMapLinear).
pose hKInner:=restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) K.
pose hSInner:=restricted_inner_productP (@euclidean_inner_productP R d) S.
pose hTInner:=restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) T.
pose hPInner:=product_inner_productP hKInner hSInner.
have [hs hScale]:=euclidean_stiefel_half_normalization R.
have hPair v u (hu:S u):euclidean_hom_inner_product (L v) (L u)= 2*euclidean_inner_product v u.
  rewrite (@spherical_horizontal_lift_pairing R (1+d) idV (L u) c (J v) hId
    (@spherical_horizontal_lift_tangent R (1+d) idV c (J u) hId)) (hEval u) hJ.
  reflexivity.
have hCross v z (hz:K z):euclidean_hom_inner_product (L v) z=0.
  have [hzG hzC]:=(hK z).1 hz.
  by rewrite (@spherical_horizontal_lift_pairing R (1+d) idV z c (J v) hId hzG) hzC
    (bil0r (inner_bilinear (@euclidean_inner_productP R (1+d)))) mulr0.
have hOrthogonal:is_orthogonal_map (product_inner hKInner hSInner)
    (@restricted_inner_product R H (@euclidean_hom_inner_product R (1+d) (1+d)) T) (hom_as_linear i).
  move=>x y.
  change (euclidean_hom_inner_product (G (subspace_val x.1+s*:L (subspace_val x.2)))
    (G (subspace_val y.1+s*:L (subspace_val y.2)))=product_inner hKInner hSInner x y).
  rewrite hLeftPair.
  rewrite product_innerE
    (bilDl (inner_bilinear (@euclidean_hom_inner_productP R (1+d) (1+d))))
    !(bilDr (inner_bilinear (@euclidean_hom_inner_productP R (1+d) (1+d))))
    !(bilZl (inner_bilinear (@euclidean_hom_inner_productP R (1+d) (1+d))))
    !(bilZr (inner_bilinear (@euclidean_hom_inner_productP R (1+d) (1+d)))).
  rewrite (hCross _ _ (subspace_valP y.1))
    (inner_symmetric (@euclidean_hom_inner_productP R (1+d) (1+d)) (subspace_val x.1) (L (subspace_val y.2)))
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
  pose w0:=hom_comp (euclidean_rectangular_adjoint g) (subspace_val w).
  have hwPerp:=@spherical_gram_tangent_evaluation_perpendicular R (1+d) idV w0 c hwG.
  have hRestore:J (C (w0 c))=w0 c.
    apply:(spherical_transverse_coordinates_inverse hQ); by rewrite hQc.
  have [z [hzG [hzC [hSum hOrth]]]]:=@spherical_gram_tangent_orthogonal_split R (1+d) idV w0 c hId hc hwG.
  have hz:K z:=(hK z).2 (conj hzG hzC).
  have hu:S (Num.sqrt (2:R)*:C (w0 c)):=subspace_scale _ hwS.
  exists (@subspace_lift R H K z hz,@subspace_lift R (R_n R d) S _ hu).
  apply:subspace_val_injective.
  change (G (z+s*:L (Num.sqrt (2:R)*:C (w0 c)))=subspace_val w).
  rewrite (linZ hLLinear) scalerA /s mulVf ?scale1r.
  - rewrite /L hRestore -hSum; exact (hCancelReverse (subspace_val w)).
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
