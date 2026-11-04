(** Federer (1969), 3.2.47, p. 282: exact product
    chart on Phi^-1[e(U)]. This application discharges
    the algebraic inverse laws with the actual sealed section;
    no trivial-bundle or section-existence hypothesis is added. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanHomInnerCharts
  InnerNorm HilbertFormCompactness LinearBasis OrthonormalFamilies OrthogonalMaps
  PartialFunctionUP EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  NormRegularity SphericalOrthogonalSectionUP SphericalOrthogonalSection
  SphericalOrthogonalSectionValues SphericalOrthogonalSectionSmooth SphericalOrthogonalProductAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_section_representative_graph]: a total
    representative preserving the sealed section has its exact
    value at every original u in U, supporting the
    product chart of 3.2.47, p. 282. *)
Lemma spherical_section_representative_graph (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (F:R_n R n.+1->Hom (R_n R n.+1) (R_n R n.+1)):
  (forall u L,partial_function_graph (spherical_orthogonal_section he) u L ->F u=L) ->
  forall u,spherical_frame_patch e u ->
    partial_function_graph (spherical_orthogonal_section he) u (F u).
Proof.
move=>hAgreement u hu.
have hDomain:partial_function_domain (spherical_orthogonal_section he) u.
  by rewrite spherical_orthogonal_section_domain.
have [L hL]:=hDomain.
rewrite (hAgreement u L hL); exact hL.
Qed.

(** Source for [spherical_orthogonal_product_chart_exists]: the actual
    section of 3.2.47, p. 282, supplies mutually
    inverse product coordinates on every translated original patch.
    This theorem proves the exact domains, orthogonal membership,
    isotropy membership and both inverse identities, retaining both
    hemispheres. The ambient section representative is smooth;
    product-map regularity is established separately. *)
Theorem spherical_orthogonal_product_chart_exists (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e)
    (t:Hom (R_n R n.+1) (R_n R n.+1)):
  is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) (hom_as_linear t) ->
  exists F:R_n R n.+1->Hom (R_n R n.+1) (R_n R n.+1),
    norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
      (inner_norm_real_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
      (spherical_frame_cone e) F /\
    (forall g:Hom (R_n R n.+1) (R_n R n.+1),
      is_orthogonal_map (@euclidean_inner_product R n.+1)
        (@euclidean_inner_product R n.+1) (hom_as_linear g) ->
      spherical_frame_patch e (euclidean_rectangular_adjoint t (g (e ord0))) ->
      let f:=F (euclidean_rectangular_adjoint t (g (e ord0))) in
      spherical_orthogonal_isotropy (e ord0) (spherical_section_product_coordinate t f g) /\
      spherical_section_product_inverse t f (spherical_section_product_coordinate t f g)=g) /\
    (forall (a:R_n R n.+1) (h:Hom (R_n R n.+1) (R_n R n.+1)),
      spherical_frame_patch e (euclidean_rectangular_adjoint t a) ->
      spherical_orthogonal_isotropy (e ord0) h ->
      let g:=spherical_section_product_inverse t (F (euclidean_rectangular_adjoint t a)) h in
      is_orthogonal_map (@euclidean_inner_product R n.+1)
        (@euclidean_inner_product R n.+1) (hom_as_linear g) /\
      g (e ord0)=a /\
      spherical_frame_patch e (euclidean_rectangular_adjoint t (g (e ord0))) /\
      spherical_section_product_coordinate t
        (F (euclidean_rectangular_adjoint t (g (e ord0)))) g=h).
Proof.
move=>ht.
have [F [hSmooth [hOrthogonal hAgreement]]]:=
  @spherical_orthogonal_section_smooth_representative R n e he hON.
have hGraph u (hu:spherical_frame_patch e u):
    partial_function_graph (spherical_orthogonal_section he) u (F u).
  exact (@spherical_section_representative_graph R n e he F hAgreement u hu).
have hFirst u (hu:spherical_frame_patch e u):F u (e ord0)=u.
  exact (@spherical_section_first_vector R n e he u (F u) (hGraph u hu)).
have hOrtho u (hu:spherical_frame_patch e u):
    is_orthogonal_map (@euclidean_inner_product R n.+1)
      (@euclidean_inner_product R n.+1) (hom_as_linear (F u)).
  exact (@spherical_section_orthogonal R n e he hON u (F u) (hGraph u hu)).
exists F; split; first exact hSmooth.
split.
- move=>g hg hPatch f; split.
  + exact (@spherical_section_product_coordinate_member R n.+1 (e ord0) t f g
      ht (hOrtho _ hPatch) hg (hFirst _ hPatch)).
  + exact (@spherical_section_product_left_inverse R n.+1 t f g ht (hOrtho _ hPatch)).
- move=>a h hPatch hIsotropy g.
  have hF:=hOrtho _ hPatch.
  have hValue:=hFirst _ hPatch.
  have hBase:g (e ord0)=a.
    exact (@spherical_section_product_base_value R n.+1 (e ord0) a t
      (F (euclidean_rectangular_adjoint t a)) h ht hValue hIsotropy).
  split.
  + move=>x y; change (euclidean_inner_product
      (t (F (euclidean_rectangular_adjoint t a) (h x)))
      (t (F (euclidean_rectangular_adjoint t a) (h y)))=euclidean_inner_product x y).
    by rewrite ht hF hIsotropy.1.
  + split; first exact hBase.
    split; first by rewrite hBase.
    rewrite hBase.
    exact (@spherical_section_product_right_inverse R n.+1 t
      (F (euclidean_rectangular_adjoint t a)) h ht hF).
Qed.
