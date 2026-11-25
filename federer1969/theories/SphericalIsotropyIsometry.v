(** Federer (1969), 3.2.47, pp. 282–283: the
    actual fibre I at any original unit c is isometric
    to O(n-1) with its original Hilbert Hom metric.
    The coordinate pole and orthogonal change remain local witnesses;
    no globally selected frame or abstract isometry premise is added. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerNormalization OrthonormalFamilies OrthogonalMaps
  EuclideanHomInnerCharts EuclideanStiefelInnerSplitting UnitVectorOrthogonalMap
  EuclideanBlockExtension EuclideanBlockHomDifference SphericalOrthogonalProductAlgebra
  SphericalCoordinateIsotropy SphericalIsotropyConjugacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_isotropy_isometric_parametrization]: the
    exact I isometric with O(n-1) in 3.2.47,
    pp. 282–283. A global inverse for the ambient
    affine isometric embedding and its exact orthogonal image are
    supplied. Dimension n-1=0 retains the unit atom. *)
Theorem spherical_isotropy_isometric_parametrization (R:realType) n (c:R_n R (1+n)):
  inner_norm (@euclidean_inner_productP R (1+n)) c= 1 ->
  exists (F:Hom (R_n R n) (R_n R n)->Hom (R_n R (1+n)) (R_n R (1+n)))
    (G:Hom (R_n R (1+n)) (R_n R (1+n))->Hom (R_n R n) (R_n R n)),
    cancel F G /\
    (forall h g,inner_norm (@euclidean_hom_inner_productP R (1+n) (1+n)) (F h-F g)=
      inner_norm (@euclidean_hom_inner_productP R n n) (h-g)) /\
    F @` [set h:Hom (R_n R n) (R_n R n)|
      is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear h)]=
      spherical_orthogonal_isotropy c.
Proof.
move=>hc.
pose p:=spherical_coordinate_pole R n.
have hp:inner_norm (@euclidean_inner_productP R (1+n)) p= 1.
  exact (@orthonormal_norm1 R (R_n R (1+n)) (@euclidean_inner_product R (1+n))
    (@euclidean_inner_productP R (1+n)) (Finite.clone 'I_(1+n) _)
    (@coordinate_basis R (1+n)) (@euclidean_coordinate_orthonormal_family R (1+n))
    (lshift n (ord0:'I_1))).
have hPos:(0<1+n)%N by rewrite add1n ltn0Sn.
have [q [hq hAxis]]:=@unit_vector_orthogonal_map_exists R (1+n) p c hPos hp hc.
pose Q:=hom_of_linear q.
have hQ:is_orthogonal_map (@euclidean_inner_product R (1+n))
    (@euclidean_inner_product R (1+n)) (hom_as_linear Q) by exact hq.
have hPole:Q p=c by exact hAxis.
pose E:=fun h:Hom (R_n R n) (R_n R n)=>
  hom_of_linear (@euclidean_block_extension R 1 n (hom_as_linear h)).
pose F:=fun h=>spherical_isotropy_conjugate Q (E h).
pose G:=fun H:Hom (R_n R (1+n)) (R_n R (1+n))=>
  spherical_coordinate_restriction (spherical_isotropy_unconjugate Q H).
have hG H (hH:spherical_orthogonal_isotropy c H):
    spherical_orthogonal_isotropy p (spherical_isotropy_unconjugate Q H).
  have hHH:spherical_orthogonal_isotropy (Q p) H by rewrite hPole.
  exact (@spherical_isotropy_unconjugacy_member R (1+n) p Q H hQ hHH).
have hMember h (hh:is_orthogonal_map (@euclidean_inner_product R n)
    (@euclidean_inner_product R n) (hom_as_linear h)):
    spherical_orthogonal_isotropy c (F h).
  have hCoordinate:=@spherical_coordinate_extension_member R n h hh.
  have hConjugate:=@spherical_isotropy_conjugacy_member R (1+n) p Q (E h) hQ hCoordinate.
  by rewrite hPole in hConjugate.
have hInverse H (hH:spherical_orthogonal_isotropy c H):F (G H)=H.
  have hReconstruct:=@spherical_coordinate_isotropy_reconstruction R n
    (spherical_isotropy_unconjugate Q H) (hG H hH).
  exact (eq_trans (congr1 (spherical_isotropy_conjugate Q) hReconstruct)
    (@spherical_isotropy_conjugacy_cancel_reverse R (1+n) Q hQ H)).
exists F,G; split.
- move=>h; change (spherical_coordinate_restriction
    (spherical_isotropy_unconjugate Q (spherical_isotropy_conjugate Q (E h)))=h).
  rewrite (spherical_isotropy_conjugacy_cancel hQ).
  exact (@spherical_coordinate_restriction_extension R n h).
- split.
  + move=>h g.
    exact (eq_trans (@spherical_isotropy_conjugacy_distance R (1+n) Q (E h) (E g) hQ)
      (@euclidean_block_extension_difference_norm R 1 n h g)).
  + apply/seteqP; split=>H.
    * move=>[h hh <-]; exact:hMember h hh.
    * move=>hH; exists (G H).
      -- exact (@spherical_coordinate_isotropy_restriction_orthogonal R n
           (spherical_isotropy_unconjugate Q H) (hG H hH)).
      -- exact:hInverse H hH.
Qed.
