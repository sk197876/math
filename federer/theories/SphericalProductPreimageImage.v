(** Federer (1969), 3.2.47, pp. 282–283: the actual
    smooth inverse chart maps E times I exactly onto the
    original orthogonal-group preimage, whenever E lies in its
    translated patch. Every section law is discharged by the
    proved normalized section; no bundle premise is added. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness OrthogonalMaps LinearBasis OrthonormalFamilies
  EuclideanHomInnerCharts EuclideanRectangularAdjoint NormRegularity
  SphericalOrthogonalSectionUP SphericalOrthogonalProductAlgebra
  SphericalOrthogonalProductChart SphericalOrthogonalProductSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_orthogonal_preimage]: the original
    Phi inverse(E) of 3.2.47, p. 283, retaining
    actual orthogonal operators and their original values at c. *)
Definition spherical_orthogonal_preimage (R:realType) N (c:R_n R N) (E:set (R_n R N)):
    set (Hom (R_n R N) (R_n R N)):=
  [set g|is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) /\E (g c)].

(** Source for [spherical_product_preimage_image_exists]: the
    exact image assertion of the printed product diffeomorphism,
    3.2.47, pp. 282–283, for arbitrary original E
    in the patch. The auxiliary smooth representative stays local. *)
Theorem spherical_product_preimage_image_exists (R:realType) n
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
    forall E:set (R_n R n.+1),
      (forall a,E a ->spherical_frame_patch e (euclidean_rectangular_adjoint t a)) ->
      (fun z:R_n R n.+1*Hom (R_n R n.+1) (R_n R n.+1)=>
        spherical_section_product_inverse t (F (euclidean_rectangular_adjoint t z.1)) z.2) @`
        [set z|E z.1 /\spherical_orthogonal_isotropy (e ord0) z.2]=
      spherical_orthogonal_preimage (e ord0) E.
Proof.
move=>ht.
have [F [hSmooth [hForward hBackward]]]:=
  @spherical_orthogonal_product_chart_exists R n e he hON t ht.
exists F; split; first exact hSmooth.
move=>E hE; apply/seteqP; split=>g.
- move=>[[a h] [ha hI] <-].
  have [hO [hValue _]]:=hBackward a h (hE a ha) hI.
  split; first exact hO.
  by rewrite hValue.
- move=>[hg hEg].
  have [hI hInverse]:=hForward g hg (hE _ hEg).
  exists (g (e ord0),spherical_section_product_coordinate t
    (F (euclidean_rectangular_adjoint t (g (e ord0)))) g).
  + by split.
  + exact hInverse.
Qed.
