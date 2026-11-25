(** Federer (1969), 3.2.48, p. 285: the target direct sum
    Tan(I,1) plus W(1), embedded in the original Hilbert Hom space.
    The actual normalized horizontal lift gives its isometry. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets ring.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerProductLaws
  InnerProductRestriction InnerNorm EuclideanHomInnerCharts OrthogonalMaps ProductInner
  EuclideanGramDifferentialAlgebra SphericalHorizontalLift SphericalHorizontalLiftLinear
  EuclideanStiefelHalfNormalization SphericalTangentCoordinates SphericalCoordinateIsotropy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [spherical_kinematic_target_embedding]: the target
    vertical direct sum arrow in 3.2.48, p. 285, expressed by the
    actual vertical inclusion and normalized horizontal lift. *)
Definition spherical_kinematic_target_embedding (R:realType) d (c:R_n R (1+d))
    (Q:Hom (R_n R (1+d)) (R_n R (1+d)))
    (K:subspace (Hom (R_n R (1+d)) (R_n R (1+d))))
    (x:subspace_space K*R_n R d):=
  subspace_val x.1+(Num.sqrt (2:R))^-1*:
    spherical_horizontal_lift (hom_of_linear (linear_id (R_n R (1+d)))) c
      (spherical_transverse_embedding Q x.2).

Arguments spherical_kinematic_target_embedding {R d} c Q K x.

(** Source for [spherical_kinematic_target_embedding_linear]: linearity
    of the actual target direct sum arrow in 3.2.48, p. 285. *)
Lemma spherical_kinematic_target_embedding_linear (R:realType) d (c:R_n R (1+d))
    (Q:Hom (R_n R (1+d)) (R_n R (1+d)))
    (K:subspace (Hom (R_n R (1+d)) (R_n R (1+d)))):
  linear (spherical_kinematic_target_embedding c Q K).
Proof.
pose idV:Hom (R_n R (1+d)) (R_n R (1+d)):=hom_of_linear (linear_id (R_n R (1+d))).
pose J:=spherical_transverse_embedding Q.
pose L:=spherical_horizontal_lift idV c.
have hL:linear L:=spherical_horizontal_lift_linear idV c.
move=>a x y; rewrite /spherical_kinematic_target_embedding.
change (a*:subspace_val x.1+subspace_val y.1+(Num.sqrt (2:R))^-1*:L (J (a*:x.2+y.2))=
  a*:(subspace_val x.1+(Num.sqrt (2:R))^-1*:L (J x.2))+
    (subspace_val y.1+(Num.sqrt (2:R))^-1*:L (J y.2))).
rewrite (hom_linear J) (hL a (J x.2) (J y.2)) !scalerDr !scalerA.
by rewrite [((Num.sqrt (2:R))^-1)*a]mulrC addrACA.
Qed.

(** Source for [spherical_kinematic_target_embedding_hom]: the same
    actual linear direct sum arrow, supporting 3.2.48, p. 285. *)
Definition spherical_kinematic_target_embedding_hom (R:realType) d (c:R_n R (1+d))
    (Q:Hom (R_n R (1+d)) (R_n R (1+d)))
    (K:subspace (Hom (R_n R (1+d)) (R_n R (1+d)))):
    Hom [the lmodType R of (subspace_space K*R_n R d)%type]
      (Hom (R_n R (1+d)) (R_n R (1+d))):=
  @HomMap R _ _ (spherical_kinematic_target_embedding c Q K)
    (introT (asboolP _) (@spherical_kinematic_target_embedding_linear R d c Q K)).

Arguments spherical_kinematic_target_embedding_hom {R d} c Q K.

(** Source for [spherical_kinematic_target_embedding_orthogonal]: the
    actual target arrow is isometric, 3.2.48, p. 285. The vertical
    Gram kernel is orthogonal to the lift and the transverse lift pairing
    is twice the original pairing; normalization removes this factor. *)
Theorem spherical_kinematic_target_embedding_orthogonal (R:realType) d (c:R_n R (1+d))
    (Q:Hom (R_n R (1+d)) (R_n R (1+d)))
    (K:subspace (Hom (R_n R (1+d)) (R_n R (1+d)))):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  Q (spherical_coordinate_pole R d)=c ->
  (forall w,K w ->euclidean_gram_differential (hom_of_linear (linear_id (R_n R (1+d)))) w=0 /\w c=0) ->
  is_orthogonal_map
    (product_inner (restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) K)
      (@euclidean_inner_productP R d))
    (@euclidean_hom_inner_product R (1+d) (1+d))
    (hom_as_linear (spherical_kinematic_target_embedding_hom c Q K)).
Proof.
move=>hc hQ hQc hK.
pose idV:Hom (R_n R (1+d)) (R_n R (1+d)):=hom_of_linear (linear_id (R_n R (1+d))).
pose J:=spherical_transverse_embedding Q.
pose L:=fun v:R_n R d=>spherical_horizontal_lift idV c (J v).
pose s:=(Num.sqrt (2:R))^-1.
have hId:is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear idV) by move=>x y.
have hUnit:euclidean_inner_product c c= 1.
  by rewrite -(inner_norm_sqr (@euclidean_inner_productP R (1+d))) hc expr1n.
have hPerp v:euclidean_inner_product c (J v)=0.
  by rewrite -hQc; exact (spherical_transverse_embedding_perpendicular hQ v).
have hPair v u:euclidean_hom_inner_product (L v) (L u)= 2*euclidean_inner_product v u.
  rewrite (@spherical_horizontal_lift_pairing R (1+d) idV (L u) c (J v) hId
    (@spherical_horizontal_lift_tangent R (1+d) idV c (J u) hId))
    (@spherical_horizontal_lift_evaluation R (1+d) idV c (J u) hUnit (hPerp u)).
  by rewrite (spherical_transverse_embedding_orthogonal hQ).
have hCross v z (hz:K z):euclidean_hom_inner_product (L v) z=0.
  have [hzG hzC]:=hK z hz.
  by rewrite (@spherical_horizontal_lift_pairing R (1+d) idV z c (J v) hId hzG) hzC
    (bil0r (inner_bilinear (@euclidean_inner_productP R (1+d)))) mulr0.
have [_ hScale]:=euclidean_stiefel_half_normalization R.
move=>x y.
change (euclidean_hom_inner_product (subspace_val x.1+s*:L x.2) (subspace_val y.1+s*:L y.2)=
  product_inner (restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) K)
    (@euclidean_inner_productP R d) x y).
rewrite product_innerE
  (bilDl (inner_bilinear (@euclidean_hom_inner_productP R (1+d) (1+d))))
  !(bilDr (inner_bilinear (@euclidean_hom_inner_productP R (1+d) (1+d))))
  !(bilZl (inner_bilinear (@euclidean_hom_inner_productP R (1+d) (1+d))))
  !(bilZr (inner_bilinear (@euclidean_hom_inner_productP R (1+d) (1+d)))).
rewrite (hCross _ _ (subspace_valP y.1))
  (inner_symmetric (@euclidean_hom_inner_productP R (1+d) (1+d)) (subspace_val x.1) (L y.2))
  (hCross _ _ (subspace_valP x.1)) hPair !scaler0 !addr0 ?add0r.
change (euclidean_hom_inner_product (subspace_val x.1) (subspace_val y.1)+
  s*(s*(2*euclidean_inner_product x.2 y.2))=
  euclidean_hom_inner_product (subspace_val x.1) (subspace_val y.1)+euclidean_inner_product x.2 y.2).
have hFactor:s*(s*(2*euclidean_inner_product x.2 y.2))=(2*s*s)*euclidean_inner_product x.2 y.2 by ring.
by rewrite hFactor hScale mul1r.
Qed.
