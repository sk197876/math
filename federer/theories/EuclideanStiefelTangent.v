(** Federer (1969), 3.2.28(1), printed p. 263:
    the actual tangent cone of O(n,m) is precisely
    the displayed Gram kernel. No geometric tangent law
    is built into the definition of the algebraic kernel. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  InnerProductUP OrthogonalMaps HilbertFormCompactness HomCompositionDeterminant
  NormedSubspace EuclideanRectangularAdjoint EuclideanHomInnerCharts
  EuclideanGramDifferentialAlgebra EuclideanSymmetricEndomorphismSpace
  EuclideanSymmetricDimension EuclideanSymmetricGram EuclideanSymmetricGramField
  FiniteInnerRegularTangent TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_stiefel_tangent]: the exact equation
    Tan[O(n,m),g]={h:h* g+g* h=0}, Federer
    3.2.28(1), p. 263, for every actual orthogonal
    injection g. All dimensions, including zero, are retained. *)
Theorem euclidean_stiefel_tangent (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R m n))
    [set f:Hom (R_n R m) (R_n R n)|
      is_orthogonal_map (@euclidean_inner_product R m)
        (@euclidean_inner_product R n) (hom_as_linear f)] g=
    [set h|hom_comp (euclidean_rectangular_adjoint h) g+
      hom_comp (euclidean_rectangular_adjoint g) h=0].
Proof.
move=>hg.
pose X:=Hom (R_n R m) (R_n R n).
pose E:=Hom (R_n R m) (R_n R m).
pose S:=@euclidean_symmetric_hom_subspace R m.
pose Y:=subspace_space S.
pose B:=@euclidean_hom_inner_product R m n.
pose hB:=@euclidean_hom_inner_productP R m n.
pose NE:=inner_norm (@euclidean_hom_inner_productP R m m).
pose NY:=subspace_norm NE S.
pose hNY:=subspace_norm_laws
  (inner_norm_real_norm (@euclidean_hom_inner_productP R m m)) S.
have hInject:=@orthogonal_map_injective R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  (hom_as_linear g) hg.
have hSurj:=@euclidean_symmetric_gram_differential_surjective R m n g hInject.
have [d hd]:=@euclidean_symmetric_dimension_basis R m.
have hT:=@finite_inner_regular_fibre_tangent R X Y B hB NY hNY
  _ _ (@hom_rank_one_baseP R (R_n R m) (R_n R n) m n
    (@coordinate_basis R m) (@coordinate_basisP R m)
    (@coordinate_basis R n) (@coordinate_basisP R n))
  _ d hd (@euclidean_symmetric_gram R m n)
  (@euclidean_symmetric_gram_differential R m n) g
  (@euclidean_symmetric_gram_class_one_field R m n) hSurj.
have hGramG:euclidean_gram_map g=hom_of_linear (linear_id (R_n R m)):=
  (euclidean_gram_orthogonal_level g).1 hg.
have hSet:[set f:X|euclidean_symmetric_gram f=euclidean_symmetric_gram g]=
    [set f:X|is_orthogonal_map (@euclidean_inner_product R m)
      (@euclidean_inner_product R n) (hom_as_linear f)].
  apply/seteqP; split=>f.
  - move=>hf; apply:(euclidean_gram_orthogonal_level f).2.
    have hh:=congr1 (@subspace_val R E S) hf.
    by rewrite !euclidean_symmetric_gramE hGramG in hh.
  - move=>hf; apply:subspace_val_injective.
    rewrite !euclidean_symmetric_gramE hGramG.
    exact:(euclidean_gram_orthogonal_level f).1 hf.
have hKernel:[set h:X|euclidean_symmetric_gram_differential g h=0]=
    [set h:X|hom_comp (euclidean_rectangular_adjoint h) g+
      hom_comp (euclidean_rectangular_adjoint g) h=0].
  apply/seteqP; split=>h.
  - move=>hz; have hh:=congr1 (@subspace_val R E S) hz.
    by rewrite euclidean_symmetric_gram_differentialE
      euclidean_gram_differentialE linear0 in hh.
  - move=>hz; apply:subspace_val_injective.
    by rewrite euclidean_symmetric_gram_differentialE
      euclidean_gram_differentialE linear0.
by rewrite hSet hKernel in hT.
Qed.
