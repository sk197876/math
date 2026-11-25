(** Federer (1969), 3.2.28(2), printed pp. 264–265:
    each fibre of Q is exactly the isometric image of SO(m)
    under u to g u. The algebraic identification below
    precedes all claims about fibre Hausdorff measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient Bilinear GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerNorm OrthogonalMaps AdjointUP AdjointCriteria
  EuclideanRectangularAdjoint ExteriorGrading ExteriorMaps ExteriorMapScaling
  ExteriorOperatorEstimate ExteriorNorm ExteriorDeterminant FiniteExteriorPowers
  AssociatedSubspace SimpleProducts FrameImageSpan
  EuclideanExteriorWordSmooth EuclideanExteriorWordEvaluation EuclideanExteriorWordImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_special_orthogonal_set]: SO(m) is
    the set of orthogonal endomorphisms with determinant one,
    as used in Federer 3.2.28(2), p. 264.
    The determinant is the sealed exterior-action definition
    of 1.3.4, p. 16; no orientation convention is added. *)
Definition euclidean_special_orthogonal_set (R:realType) m:
    set (Hom (R_n R m) (R_n R m)):=
  [set u|is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R m) (hom_as_linear u) /\
    det (euclidean_two_nonzero R) (@coordinate_basisP R m) (hom_as_linear u)= 1].

(** Source for [euclidean_exterior_frame_associated_range]:
    the m-plane associated with Q(g) is the actual image
    of g, 1.6.2 and 1.7.7, pp. 24 and 34, used in
    the fibre identification of Federer 3.2.28(2), p. 265. *)
Lemma euclidean_exterior_frame_associated_range (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  forall v,FedererSimple.T (euclidean_exterior_word_map g) v <->exists x,g x=v.
Proof.
move=>hg v.
have [hs hn]:=euclidean_exterior_word_frame_unit hg.
have hNz:euclidean_exterior_word_map g!=0.
  apply/eqP=>hz; move:hn; rewrite hz exterior_norm_zero=>/eqP.
  by rewrite eq_sym oner_eq0.
rewrite euclidean_exterior_word_mapE exterior_map_indexed_product in hNz *.
rewrite (product_associated_space (euclidean_two_nonzero R) hNz).
symmetry.
exact:(@basis_image_finite_span R (R_n R m) (R_n R n) m
  (@coordinate_basis R m) (@coordinate_basisP R m)
  (fun i=>g (@coordinate_basis R m i)) (hom_as_linear g) (fun _=>erefl _) v).
Qed.

(** Source for [euclidean_exterior_frame_right_action]:
    Q(g u)=det(u) Q(g), supporting constancy on SO(m)
    in Federer 3.2.28(2), pp. 264–265, by the
    top exterior determinant definition of 1.3.4, p. 16. *)
Lemma euclidean_exterior_frame_right_action (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)) (u:Hom (R_n R m) (R_n R m)):
  euclidean_exterior_word_map (hom_comp g u)=
    det (euclidean_two_nonzero R) (@coordinate_basisP R m) (hom_as_linear u)*:
      euclidean_exterior_word_map g.
Proof.
rewrite !euclidean_exterior_word_mapE.
have hEq:hom_as_linear (hom_comp g u)=1 linear_comp (hom_as_linear g) (hom_as_linear u)
  by move=>x.
rewrite (exterior_power_map_ext hEq) -exterior_power_map_composition
  (@detE R (euclidean_two_nonzero R) m (R_n R m) (@coordinate_basis R m)
    (@coordinate_basisP R m) (hom_as_linear u)
    (e_lambda (@coordinate_basis R m) (ord_tuple m))) linearZ.
reflexivity.
Qed.

(** Source for [euclidean_exterior_frame_fibre_special_orthogonal]:
    Q inverse Q(g) is exactly R_g(SO(m)), Federer
    3.2.28(2), p. 265. The parameter u=g* h
    is derived from equality of the actual associated planes;
    orthogonality and determinant one are proved. The algebra
    also covers m=0; the later half-volume law requires m>0. *)
Theorem euclidean_exterior_frame_fibre_special_orthogonal (R:realType) m n
    (g h:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear h) ->
  (euclidean_exterior_word_map h=euclidean_exterior_word_map g <->
    exists u,euclidean_special_orthogonal_set u /\h=hom_comp g u).
Proof.
move=>hg hh; split.
- move=>hQ.
  have hCan:cancel g (euclidean_rectangular_adjoint g).
    exact:(orthogonal_iff_adjoint_left_inverse (@euclidean_inner_productP R m)
      (euclidean_rectangular_adjoint_pairing g)).1 hg.
  pose u:=hom_comp (euclidean_rectangular_adjoint g) h.
  have hRange x:exists y,g y=h x.
    apply:(euclidean_exterior_frame_associated_range hg (h x)).1.
    rewrite -hQ.
    apply:(euclidean_exterior_frame_associated_range hh (h x)).2.
    by exists x.
  have hGH:hom_comp g u=h.
    apply:hom_ext=>x; have [y hy]:=hRange x.
    change (g (euclidean_rectangular_adjoint g (h x))=h x).
    by rewrite -hy hCan.
  have hU:is_orthogonal_map (@euclidean_inner_product R m)
      (@euclidean_inner_product R m) (hom_as_linear u).
    move=>x y; rewrite -hg.
    change (euclidean_inner_product (hom_comp g u x) (hom_comp g u y)=euclidean_inner_product x y).
    by rewrite hGH hh.
  have [hs hn]:=euclidean_exterior_word_frame_unit hg.
  have hNz:euclidean_exterior_word_map g!=0.
    apply/eqP=>hz; move:hn; rewrite hz exterior_norm_zero=>/eqP.
    by rewrite eq_sym oner_eq0.
  have hScalar:(det (euclidean_two_nonzero R) (@coordinate_basisP R m) (hom_as_linear u)-1)*:
      euclidean_exterior_word_map g=0.
    by rewrite scalerBl scale1r -euclidean_exterior_frame_right_action hGH hQ subrr.
  have hDet:det (euclidean_two_nonzero R) (@coordinate_basisP R m) (hom_as_linear u)= 1.
    move/eqP:hScalar; rewrite scaler_eq0 (negbTE hNz) orbF subr_eq0=>/eqP; exact.
  exists u; split; last exact:esym hGH.
  exact:(conj hU hDet).
- move=>[u [[hu hd] ->]].
  by rewrite euclidean_exterior_frame_right_action hd scale1r.
Qed.
