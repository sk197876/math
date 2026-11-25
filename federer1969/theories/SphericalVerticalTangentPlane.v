(** Federer (1969), 3.2.48, p. 285: the actual
    common vertical space Tan(I,1) has dimension mu.
    Supporting the first subtraction block: actual smooth
    isotropy charts and the proved 3.2.47 tangent law
    identify its Gram-and-evaluation equations, including mu=0. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  HomCompositionDeterminant EuclideanHomInnerCharts OrthogonalMaps
  GrassmannSubspaces LinearBasis EuclideanGramDifferentialAlgebra
  FiniteInnerTangentPlane FiniteInnerSmoothSubmanifoldUP
  SphericalIsotropySmoothSubmanifold SphericalOrthogonalProductAlgebra
  SphericalOrthogonalTangentTranslation SphericalOrthogonalTangents TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_vertical_tangent_plane]: the actual
    mu-dimensional vertical summand Tan(I,1) in 3.2.48,
    p. 285. Its plane and dimension are proved
    from the original isotropy, not supplied as a
    tangent or rank hypothesis. All auxiliary bases remain local. *)
Theorem spherical_vertical_tangent_plane (R:realType) d (c:R_n R d.+1):
  inner_norm (@euclidean_inner_productP R d.+1) c= 1 ->
  exists K:G (Hom (R_n R d.+1) (R_n R d.+1)) (d*(d-1)%/2)%N,
    [set w|euclidean_gram_differential (hom_of_linear (linear_id (R_n R d.+1))) w=0 /\
      w c=0]=(grassmann_val K:set _).
Proof.
move=>hc.
pose V:=R_n R d.+1.
pose H:=Hom V V.
pose identity:Hom V V:=hom_of_linear (linear_id V).
have hIdentity:is_orthogonal_map (@euclidean_inner_product R d.+1)
    (@euclidean_inner_product R d.+1) (hom_as_linear identity) by move=>x y.
have hI:spherical_orthogonal_isotropy c identity by split.
have hSmooth:=@spherical_isotropy_smooth_submanifold R d c hc.
have hMan:=inner_smooth_submanifold_class hSmooth 1%N.
have [K hTan]:=@finite_inner_submanifold_tangent_plane R H _
  (@euclidean_hom_inner_productP R d.+1 d.+1) _
  (@hom_rank_one_base R V V d.+1 d.+1 (@coordinate_basis R d.+1)
    (@coordinate_basisP R d.+1) (@coordinate_basis R d.+1))
  (@hom_rank_one_baseP R V V d.+1 d.+1 (@coordinate_basis R d.+1)
    (@coordinate_basisP R d.+1) (@coordinate_basis R d.+1) (@coordinate_basisP R d.+1))
  (d*(d-1)%/2)%N 1%N (spherical_orthogonal_isotropy c) identity (leqnn 1) hMan hI.
have hKernel:=@spherical_vertical_tangent_left_translate R d c identity hc hIdentity.
rewrite (spherical_orthogonal_tangent_gram hIdentity) hTan in hKernel.
have hImage:(fun w=>hom_comp identity w) @` (grassmann_val K:set H)=(grassmann_val K:set H).
  apply/seteqP; split=>w.
  - move=>[z hz <-]; have hSame:hom_comp identity z=z by apply:hom_ext=>x.
    by rewrite hSame.
  - move=>hw; exists w; first exact hw.
    by apply:hom_ext=>x.
exists K; exact (eq_trans hKernel hImage).
Qed.
