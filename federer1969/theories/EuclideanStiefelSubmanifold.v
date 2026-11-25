(** Federer (1969), 3.2.28(1), printed p. 263:
    O(n,m) is the regular identity level of the actual
    symmetric Gram map, in the Hom inner product of 1.7.9. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  InnerProductUP SymmetricEndomorphisms OrthogonalMaps HilbertFormCompactness
  HomCompositionDeterminant NormedSubspace EuclideanHomInnerCharts
  EuclideanGramDifferentialAlgebra EuclideanSymmetricEndomorphismSpace
  EuclideanSymmetricDimension EuclideanSymmetricGram EuclideanSymmetricGramSmooth
  EuclideanSymmetricGramField FiniteInnerSubmanifoldUP FiniteInnerRegularFibre.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_stiefel_submanifold]: the manifold
    assertion for O(n,m) in Federer 3.2.28(1), p. 263.
    The dimension is expressed as mn-m(m+1)/2 here;
    a separate arithmetic identity gives the printed equivalent
    m(2n-m-1)/2 when m<=n. Every finite positive
    class is proved, and the zero-dimensional cases are included. *)
Theorem euclidean_stiefel_submanifold (R:realType) m n k:
  (1<=k)%N ->
  is_inner_submanifold (@euclidean_hom_inner_product R m n)
    (m*n-m*(m+1)%/2)%N k
    [set g:Hom (R_n R m) (R_n R n)|
      is_orthogonal_map (@euclidean_inner_product R m)
        (@euclidean_inner_product R n) (hom_as_linear g)].
Proof.
move=>hk.
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
pose idE:=hom_of_linear (linear_id (R_n R m)).
have hId:S idE.
  apply:(@euclidean_symmetric_hom_membership R m idE).2.
  by move=>x y.
pose c:Y:=subspace_lift hId.
have hLevel (g:X):euclidean_symmetric_gram g=c <->
    is_orthogonal_map (@euclidean_inner_product R m)
      (@euclidean_inner_product R n) (hom_as_linear g).
  split.
  - move=>he; apply:(euclidean_gram_orthogonal_level g).2.
    have hc:=congr1 (@subspace_val R E S) he.
    by rewrite euclidean_symmetric_gramE /c subspace_liftE in hc.
  - move=>hg; apply:subspace_val_injective.
    rewrite euclidean_symmetric_gramE /c subspace_liftE.
    exact:(euclidean_gram_orthogonal_level g).1 hg.
have hSurj (g:X) (hg:euclidean_symmetric_gram g=c):
    forall y:Y,exists h:X,euclidean_symmetric_gram_differential g h=y.
  have hOrth:=(hLevel g).1 hg.
  have hInject:=@orthogonal_map_injective R (R_n R m) (R_n R n)
    (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    (hom_as_linear g) hOrth.
  exact:(@euclidean_symmetric_gram_differential_surjective R m n g hInject).
have [d hd]:=@euclidean_symmetric_dimension_basis R m.
have hManifold:=@finite_inner_regular_fibre_submanifold R X Y B hB NY hNY
  _ _ (@hom_rank_one_baseP R (R_n R m) (R_n R n) m n
    (@coordinate_basis R m) (@coordinate_basisP R m)
    (@coordinate_basis R n) (@coordinate_basisP R n))
  _ d hd k (@euclidean_symmetric_gram R m n)
  (@euclidean_symmetric_gram_differential R m n) c hk
  (@euclidean_symmetric_gram_smooth R m n k)
  (@euclidean_symmetric_gram_class_one_field R m n) hSurj.
rewrite card_prod !card_ord in hManifold.
have hSet:[set g:X|euclidean_symmetric_gram g=c]=
    [set g:X|is_orthogonal_map (@euclidean_inner_product R m)
      (@euclidean_inner_product R n) (hom_as_linear g)].
  apply/seteqP; split=>g.
  - exact:(hLevel g).1.
  - exact:(hLevel g).2.
by rewrite hSet in hManifold.
Qed.
