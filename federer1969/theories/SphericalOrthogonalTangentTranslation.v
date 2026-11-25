(** Federer (1969), 3.2.47, p. 283: left translation
    of the actual orthogonal-group tangent and the actual vertical
    tangent kernel. The Hilbert Hom metric and original isotropy
    fibre are retained; linear tangent transport supplies the proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  LinearBasis HilbertFormCompactness HomCompositionDeterminant EuclideanInnerProduct InnerNorm OrthogonalMaps
  EuclideanHomInnerCharts EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  UnitSphereSpace NormFiniteLinearBound NormLinearIsomorphismTangent TangentConeUP TangentSingleton
  ZeroRectifiableManifoldCover SphericalOrthogonalProductAlgebra
  SphericalProductPreimageImage SphericalOrthogonalPreimageTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_left_translation_tangent]: tangent
    transport by g, supporting Tan(O,g)=g Tan(O,1)
    in 3.2.47, p. 283. The source subset is arbitrary;
    orthogonality gives a bounded linear inverse on the ambient Hom. *)
Lemma spherical_left_translation_tangent (R:realType) N
    (g:Hom (R_n R N) (R_n R N))
    (S:set (Hom (R_n R N) (R_n R N))) (a:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  (fun w=>hom_comp g w) @`
    norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R N N)) S a=
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R N N))
    ((fun w=>hom_comp g w) @` S) (hom_comp g a).
Proof.
move=>hg.
pose V:=R_n R N.
pose H:=Hom V V.
pose hH:=@euclidean_hom_inner_productP R N N.
pose L:Hom H H:=hom_of_linear (@hom_left_composition R V V g).
pose M:Hom H H:=hom_of_linear (@hom_left_composition R V V (euclidean_rectangular_adjoint g)).
pose b:=@hom_rank_one_base R V V N N (@coordinate_basis R N)
  (@coordinate_basisP R N) (@coordinate_basis R N).
have hb:is_basis b:=@hom_rank_one_baseP R V V N N (@coordinate_basis R N)
  (@coordinate_basisP R N) (@coordinate_basis R N) (@coordinate_basisP R N).
have hL:=@norm_finite_linear_bounded R H H _ _ (inner_norm_real_norm hH)
  (inner_norm_real_norm hH) _ b hb L.
have hM:=@norm_finite_linear_bounded R H H _ _ (inner_norm_real_norm hH)
  (inner_norm_real_norm hH) _ b hb M.
have hLM:cancel L M.
  move=>w; apply:hom_ext=>x.
  exact (@euclidean_orthogonal_adjoint_cancel R N g hg (w x)).
have hML:cancel M L.
  move=>w; apply:hom_ext=>x.
  exact (@euclidean_orthogonal_adjoint_cancel_reverse R N g hg (w x)).
exact (@norm_linear_isomorphism_tangent_image R H H _ _
  (inner_norm_real_norm hH) (inner_norm_real_norm hH) L M S a hL hM hLM hML).
Qed.

(** Source for [spherical_orthogonal_tangent_left_translate]: the
    printed Tan(O,g)=g Tan(O,1), 3.2.47, p. 283.
    Both sides are the actual tangent cones of the original group. *)
Theorem spherical_orthogonal_tangent_left_translate (R:realType) N
    (g:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R N N))
    [set h|is_orthogonal_map (@euclidean_inner_product R N)
      (@euclidean_inner_product R N) (hom_as_linear h)] g=
  (fun w=>hom_comp g w) @`
    norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R N N))
      [set h|is_orthogonal_map (@euclidean_inner_product R N)
        (@euclidean_inner_product R N) (hom_as_linear h)]
      (hom_of_linear (linear_id (R_n R N))).
Proof.
move=>hg.
pose O:=[set h:Hom (R_n R N) (R_n R N)|
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear h)].
have hImage:(fun w=>hom_comp g w) @` O=O.
  apply/seteqP; split=>w.
  - move=>[z hz <-] x y; change (euclidean_inner_product (g (z x)) (g (z y))=euclidean_inner_product x y).
    by rewrite hg hz.
  - move=>hw; exists (hom_comp (euclidean_rectangular_adjoint g) w).
    + move=>x y; change (euclidean_inner_product
        (euclidean_rectangular_adjoint g (w x)) (euclidean_rectangular_adjoint g (w y))=euclidean_inner_product x y).
      by rewrite (euclidean_orthogonal_adjoint_orthogonal hg) hw.
    + apply:hom_ext=>x; exact (@euclidean_orthogonal_adjoint_cancel_reverse R N g hg (w x)).
have hPoint:hom_comp g (hom_of_linear (linear_id (R_n R N)))=g.
  by apply:hom_ext=>x.
have hTan:=@spherical_left_translation_tangent R N g O
  (hom_of_linear (linear_id (R_n R N))) hg.
rewrite hImage hPoint in hTan; exact (esym hTan).
Qed.

(** Source for [spherical_vertical_tangent_left_translate]: the
    printed kernel of D Phi restricted to Tan(O,g) equals
    g Tan(I,1), 3.2.47, p. 283. The derivative
    is actual evaluation w(c), and I is the original stabilizer. *)
Theorem spherical_vertical_tangent_left_translate (R:realType) n
    (c:R_n R n.+1) (g:Hom (R_n R n.+1) (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) (hom_as_linear g) ->
  [set w|norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
    [set h|is_orthogonal_map (@euclidean_inner_product R n.+1)
      (@euclidean_inner_product R n.+1) (hom_as_linear h)] g w /\w c=0]=
  (fun w=>hom_comp g w) @`
    norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
      (spherical_orthogonal_isotropy c) (hom_of_linear (linear_id (R_n R n.+1))).
Proof.
move=>hc hg.
pose V:=R_n R n.+1.
pose H:=Hom V V.
pose idV:Hom V V:=hom_of_linear (linear_id V).
have hImage:(fun w=>hom_comp g w) @` spherical_orthogonal_isotropy c=
    spherical_orthogonal_preimage c [set g c].
  apply/seteqP; split=>w.
  - move=>[z [hz hzC] <-]; split.
    + move=>x y; change (euclidean_inner_product (g (z x)) (g (z y))=euclidean_inner_product x y).
      by rewrite hg hz.
    + change (g (z c)=g c); by rewrite hzC.
  - move=>[hw hwC]; exists (hom_comp (euclidean_rectangular_adjoint g) w).
    + split.
      * move=>x y; change (euclidean_inner_product
          (euclidean_rectangular_adjoint g (w x)) (euclidean_rectangular_adjoint g (w y))=euclidean_inner_product x y).
        by rewrite (euclidean_orthogonal_adjoint_orthogonal hg) hw.
      * change (euclidean_rectangular_adjoint g (w c)=c).
        by rewrite hwC (euclidean_orthogonal_adjoint_cancel hg).
    + apply:hom_ext=>x; exact (@euclidean_orthogonal_adjoint_cancel_reverse R n.+1 g hg (w x)).
have hPoint:hom_comp g idV=g by apply:hom_ext=>x.
have hTan:=@spherical_left_translation_tangent R n.+1 g
  (spherical_orthogonal_isotropy c) idV hg.
rewrite hImage hPoint in hTan.
have hSphere:[set g c] `<=` @euclidean_unit_sphere_set R n.+1.
  move=>z ->; change (inner_norm (@euclidean_inner_productP R n.+1) (g c)= 1).
  by rewrite (orthogonal_map_norm (@euclidean_inner_productP R n.+1)
    (@euclidean_inner_productP R n.+1) hg) hc.
have hPre:spherical_orthogonal_preimage c [set g c] g by split.
have hFibre:=@spherical_orthogonal_preimage_tangent R n 0%N c [set g c] g
  hc (@singleton_zero_submanifold R n.+1 1%N (g c)) hSphere hPre.
rewrite (@norm_tangent_singleton R V _ (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
  (g c)) in hFibre.
exact (eq_trans (esym hFibre) (esym hTan)).
Qed.
