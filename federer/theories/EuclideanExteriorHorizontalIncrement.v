(** Federer (1969), 3.2.28(2), p. 264:
    the exact finite horizontal increment of the
    exterior-frame map is det(I+h* h)-1. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring.
From Federer Require Import Hom TensorUP Bilinear AdjointUP AdjointLaws GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanLinearMaps EuclideanRectangularAdjoint OrthogonalMaps
  InnerProductUP InnerProductLaws InnerNorm ExteriorGrading ExteriorMaps ExteriorMapScaling
  InnerExterior InnerExteriorPositivity ExteriorNorm ExteriorFrameUnitNorm FiniteExteriorPowers ExteriorAdjoint ExteriorDeterminant
  EuclideanStiefelInnerSplitting EuclideanExteriorWordSmooth EuclideanExteriorWordEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_exterior_word_gram_pairing]: the
    adjoint-composite determinant expression behind the
    finite increment in Federer 3.2.28(2), p. 264,
    from 1.7.5–1.7.6, pp. 32–34. *)
Lemma euclidean_exterior_word_gram_pairing (R:realType) m n
    (f g:Hom (R_n R m) (R_n R n)):
  @exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m
    (euclidean_exterior_word_map f) (euclidean_exterior_word_map g)=
  euclidean_det (hom_as_linear (hom_comp (euclidean_rectangular_adjoint f) g)).
Proof.
pose h2:=euclidean_two_nonzero R.
pose z:=e_lambda (@coordinate_basis R m) (ord_tuple m).
have hUnit:exterior_norm h2 (@euclidean_inner_productP R m) z= 1.
  exact (@euclidean_top_product_unit_norm R h2 m).
have hSelf:@exterior_inner_form R h2 (R_n R m) (@euclidean_inner_product R m)
    (@euclidean_inner_productP R m) m z z= 1.
  by rewrite -(@exterior_norm_square R h2 (R_n R m) (@euclidean_inner_product R m)
    (@euclidean_inner_productP R m) m z) hUnit expr1n.
have hAdj:=@exterior_power_adjoint R h2 (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  (hom_as_linear f) (hom_as_linear (euclidean_rectangular_adjoint f))
  (euclidean_rectangular_adjoint_pairing f) m.
rewrite !euclidean_exterior_word_mapE -(hAdj z (exterior_power_map (hom_as_linear g) m z))
  exterior_power_map_composition.
rewrite (@detE R h2 m (R_n R m) (@coordinate_basis R m) (@coordinate_basisP R m)
  (linear_comp (hom_as_linear (euclidean_rectangular_adjoint f)) (hom_as_linear g)) z).
rewrite (bilZr (inner_bilinear (@exterior_inner_productP R h2 (R_n R m)
  (@euclidean_inner_product R m) (@euclidean_inner_productP R m) m))) hSelf.
change ((@det R h2 m (R_n R m) (@coordinate_basis R m) (@coordinate_basisP R m)
  (linear_comp (hom_as_linear (euclidean_rectangular_adjoint f)) (hom_as_linear g)))*(1:R)=
  euclidean_det (hom_as_linear (hom_comp (euclidean_rectangular_adjoint f) g))).
rewrite mulr1 /euclidean_det; apply:det_ext=>x; reflexivity.
Qed.

(** Source for [euclidean_stiefel_horizontal_mixed_pairing]:
    g* h=0 means every g-image is perpendicular
    to every h-image, supporting Federer 3.2.28(2),
    p. 264. *)
Lemma euclidean_stiefel_horizontal_mixed_pairing (R:realType) m n
    (g h:Hom (R_n R m) (R_n R n)):
  hom_comp (euclidean_rectangular_adjoint g) h=0 ->forall x y,
    euclidean_inner_product (g x) (h y)=0.
Proof.
move=>hZ x y; rewrite -euclidean_rectangular_adjoint_pairing.
have hy:=congr1 (fun L:Hom (R_n R m) (R_n R m)=>L y) hZ.
change (euclidean_rectangular_adjoint g (h y)=0) in hy.
by rewrite hy (bil0r (inner_bilinear (@euclidean_inner_productP R m))).
Qed.

(** Source for [euclidean_exterior_horizontal_increment]:
    the displayed exact identity |Q(g+h)-Q(g)|^2=
    det(I+h* h)-1 in Federer 3.2.28(2),
    p. 264. This retains finite increments and
    all natural degrees, independently of differentiating it. *)
Theorem euclidean_exterior_horizontal_increment (R:realType) m n
    (g h:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear g) ->
  hom_comp (euclidean_rectangular_adjoint g) h=0 ->
  (exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (euclidean_exterior_word_map (g+h)-euclidean_exterior_word_map g))^+2=
  euclidean_det (hom_as_linear (hom_of_linear (linear_id (R_n R m))+
    hom_comp (euclidean_rectangular_adjoint h) h))-1.
Proof.
move=>hG hZ.
pose idE:=hom_of_linear (linear_id (R_n R m)).
have hMixed:=euclidean_stiefel_horizontal_mixed_pairing hZ.
have hCross:hom_comp (euclidean_rectangular_adjoint g) (g+h)=idE.
  apply:hom_ext=>y; apply:(inner_vectors_ext (@euclidean_inner_productP R m))=>x.
  change (euclidean_inner_product x (euclidean_rectangular_adjoint g (g y+h y))=
    euclidean_inner_product x y).
  by rewrite euclidean_rectangular_adjoint_pairing
    (bilDr (inner_bilinear (@euclidean_inner_productP R n))) hG hMixed addr0.
have hGram:hom_comp (euclidean_rectangular_adjoint (g+h)) (g+h)=
    idE+hom_comp (euclidean_rectangular_adjoint h) h.
  apply:hom_ext=>y; apply:(inner_vectors_ext (@euclidean_inner_productP R m))=>x.
  change (euclidean_inner_product x (euclidean_rectangular_adjoint (g+h) (g y+h y))=
    euclidean_inner_product x (y+euclidean_rectangular_adjoint h (h y))).
  rewrite (bilDr (inner_bilinear (@euclidean_inner_productP R m)))
    !euclidean_rectangular_adjoint_pairing.
  change (euclidean_inner_product (g x+h x) (g y+h y)=
    euclidean_inner_product x y+euclidean_inner_product (h x) (h y)).
  rewrite (bilDl (inner_bilinear (@euclidean_inner_productP R n)))
    !(bilDr (inner_bilinear (@euclidean_inner_productP R n))) hG hMixed
    (inner_symmetric (@euclidean_inner_productP R n) (h x) (g y)) hMixed.
  by rewrite !addr0 add0r.
pose hE:=@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m.
have hGG:hom_comp (euclidean_rectangular_adjoint g) g=idE.
  apply:hom_ext=>y; apply:(inner_vectors_ext (@euclidean_inner_productP R m))=>x.
  change (euclidean_inner_product x (euclidean_rectangular_adjoint g (g y))=
    euclidean_inner_product x y).
  by rewrite euclidean_rectangular_adjoint_pairing hG.
have hDetId:euclidean_det (hom_as_linear idE)= 1.
  rewrite -(@euclidean_det_id R m) /euclidean_det; apply:det_ext=>x; reflexivity.
rewrite exterior_norm_square
  (bilBl (inner_bilinear hE)) !(bilBr (inner_bilinear hE))
  (inner_symmetric hE (euclidean_exterior_word_map (g+h)) (euclidean_exterior_word_map g))
  !euclidean_exterior_word_gram_pairing hCross hGram hGG hDetId.
ring.
Qed.
