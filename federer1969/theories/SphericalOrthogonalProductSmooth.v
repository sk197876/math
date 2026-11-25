(** Federer (1969), 3.2.47, p. 282: the actual
    product coordinate H_e and inverse (a,h) to e F(e^-1a)h
    are smooth. This follows from the proved smooth section,
    actual linear evaluation and adjoint, and actual bounded Hom
    multiplication. Product-map regularity is not an assumed bundle law. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness ProductInner ProductInnerNormBounds RealNormUP NormDifferentialUP
  NormClassOneUP NormDifferentialLinear NormFiniteLinearBound HomCompositionDeterminant
  EuclideanHomInnerCharts EuclideanRectangularAdjoint EuclideanHomRegularity
  NormRegularity NormRegularityOperations NormRegularityLinearMaps
  SphericalOrthogonalSectionUP SphericalOrthogonalOrbitDifferential SphericalOrthogonalProductAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section SmoothProduct.
Variable R:realType.
Variable n:nat.
Local Notation V:=(R_n R n.+1).
Local Notation H:=(Hom V V).
Local Notation NV:=(inner_norm (@euclidean_inner_productP R n.+1)).
Local Notation NH:=(inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1)).
Local Notation hNV:=(inner_norm_real_norm (@euclidean_inner_productP R n.+1)).
Local Notation hNH:=(inner_norm_real_norm (@euclidean_hom_inner_productP R n.+1 n.+1)).
Variable e:'I_n.+1->V.
Variable F:V->H.
Hypothesis hF:norm_class_all_orders hNV hNH (spherical_frame_cone e) F.
Variable t:H.

(** Source for [spherical_product_coordinate_smooth]: the actual
    H_e is smooth on its ambient open cone preimage,
    proving the regularity used in the printed diffeomorphism
    of 3.2.47, p. 282. No global Lipschitz constant
    on the printed open patch is asserted. *)
Theorem spherical_product_coordinate_smooth:
  norm_class_all_orders hNH hNH
    (fun g:H=>spherical_frame_cone e (euclidean_rectangular_adjoint t (g (e ord0))))
    (fun g=>spherical_section_product_coordinate t
      (F (euclidean_rectangular_adjoint t (g (e ord0)))) g).
Proof.
pose L:Hom H V:=hom_comp (euclidean_rectangular_adjoint t) (spherical_orthogonal_orbit (e ord0)).
have hL:norm_bounded_linear NH NV L.
  exact (@norm_finite_linear_bounded R H V NH NV hNH hNV _ _
    (@hom_rank_one_baseP R V V n.+1 n.+1 (@coordinate_basis R n.+1)
      (@coordinate_basisP R n.+1) (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1)) L).
pose A:=fun g:H=>spherical_frame_cone e (L g).
have hPull k:norm_class hNH hNH A (fun g=>F (L g)) k.
  exact (@norm_class_precompose_linear R H V H NH NV NH hNH hNV hNH
    (spherical_frame_cone e) F L k hL (hF k)).
have hOpen g (hg:A g):norm_domain_interior NH A g.
  exact ((@norm_class_continuous R H H NH NH hNH hNH A (fun g=>F (L g)) 0%N
    (hPull 0%N) g hg).1).
move=>k.
have hId:norm_class hNH hNH A (fun g:H=>g) k.
  apply:(@norm_class_linear R H H NH NH hNH hNH A (hom_of_linear (linear_id H)) k hOpen).
  exists 1; split; first exact:ler01.
  by move=>g; rewrite mul1r.
have hConstant:=@norm_class_constant R H H NH NH hNH hNH A (euclidean_rectangular_adjoint t) k hOpen.
have hRight:=@euclidean_hom_composition_norm_class R H NH hNH n.+1 n.+1 n.+1 A
  (fun _=>euclidean_rectangular_adjoint t) (fun g=>g) k hConstant hId.
have hLeft:=@euclidean_hom_adjoint_norm_class R H NH hNH n.+1 n.+1 A
  (fun g=>F (L g)) k (hPull k).
exact (@euclidean_hom_composition_norm_class R H NH hNH n.+1 n.+1 n.+1 A
  (fun g=>euclidean_rectangular_adjoint (F (L g)))
  (fun g=>hom_comp (euclidean_rectangular_adjoint t) g) k hLeft hRight).
Qed.

(** Source for [spherical_product_inverse_smooth]: the actual inverse
    product map is smooth for the actual Cartesian inner
    metric, proving the second regularity assertion implicit in
    the diffeomorphism of 3.2.47, p. 282. *)
Theorem spherical_product_inverse_smooth:
  norm_class_all_orders
    (inner_norm_real_norm (product_inner_productP (@euclidean_inner_productP R n.+1)
      (@euclidean_hom_inner_productP R n.+1 n.+1))) hNH
    (fun z:V*H=>spherical_frame_cone e (euclidean_rectangular_adjoint t z.1))
    (fun z=>spherical_section_product_inverse t (F (euclidean_rectangular_adjoint t z.1)) z.2).
Proof.
pose P:lmodType R:=[the lmodType R of (V*H)%type].
pose hNP:=inner_norm_real_norm (product_inner_productP (@euclidean_inner_productP R n.+1)
  (@euclidean_hom_inner_productP R n.+1 n.+1)).
pose NP:=inner_norm (product_inner_productP (@euclidean_inner_productP R n.+1)
  (@euclidean_hom_inner_productP R n.+1 n.+1)).
pose fstH:=@product_first_projection_hom R V H.
pose sndH:=@product_second_projection_hom R V H.
have hFirst:norm_bounded_linear NP NV fstH.
  exists 1; split; first exact:ler01.
  move=>z; rewrite mul1r; exact:product_inner_first_norm_bound.
have hSecond:norm_bounded_linear NP NH sndH.
  exists 1; split; first exact:ler01.
  move=>z; rewrite mul1r; exact:product_inner_second_norm_bound.
have hAdj:norm_bounded_linear NV NV (euclidean_rectangular_adjoint t).
  exact (@norm_finite_linear_bounded R V V NV NV hNV hNV n.+1
    (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1) (euclidean_rectangular_adjoint t)).
pose L:Hom P V:=hom_comp (euclidean_rectangular_adjoint t) fstH.
have hL:norm_bounded_linear NP NV L:=norm_bounded_linear_compose hFirst hAdj.
pose A:=fun z:P=>spherical_frame_cone e (L z).
have hPull k:norm_class hNP hNH A (fun z=>F (L z)) k.
  exact (@norm_class_precompose_linear R P V H NP NV NH hNP hNV hNH
    (spherical_frame_cone e) F L k hL (hF k)).
have hOpen z (hz:A z):norm_domain_interior NP A z.
  exact ((@norm_class_continuous R P H NP NH hNP hNH A (fun z=>F (L z)) 0%N
    (hPull 0%N) z hz).1).
move=>k.
have hSecondClass:=@norm_class_linear R P H NP NH hNP hNH A sndH k hOpen hSecond.
have hInner:=@euclidean_hom_composition_norm_class R P NP hNP n.+1 n.+1 n.+1 A
  (fun z=>F (L z)) sndH k (hPull k) hSecondClass.
have hConstant:=@norm_class_constant R P H NP NH hNP hNH A t k hOpen.
exact (@euclidean_hom_composition_norm_class R P NP hNP n.+1 n.+1 n.+1 A
  (fun _=>t) (fun z=>hom_comp (F (L z)) (sndH z)) k hConstant hInner).
Qed.
End SmoothProduct.
