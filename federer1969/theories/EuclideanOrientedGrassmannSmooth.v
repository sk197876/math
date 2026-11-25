(** Federer (1969), 3.2.28(2), printed pp. 264–265:
    the simple unit m-vectors form a smooth submanifold
    of dimension m(n-m) of the actual exterior Hilbert space.
    The open image and actual tangent differential rank
    supply the charts of 3.1.19(3), p. 231. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerNorm HilbertFormCompactness OrthogonalMaps
  ExteriorGrading AssociatedSubspace SimpleElementary ExteriorNorm InnerExterior InnerExteriorPositivity
  FiniteExteriorPowers FiniteOrdinalBasis LinearRankUP LinearRankTransport
  TangentConeUP NormRegularity NormClassOneUP EuclideanHomInnerCharts
  EuclideanRectangularAdjoint EuclideanGramDifferentialAlgebra EuclideanStiefelSubspaces EuclideanStiefelTangent
  EuclideanStiefelSmooth EuclideanExteriorWordSmooth EuclideanExteriorWordDifferentialField
  EuclideanExteriorTangentRank EuclideanExteriorWordImage EuclideanExteriorWordRelativeOpen
  FiniteInnerChartUP FiniteInnerChart FiniteInnerSmoothSubmanifoldUP FiniteInnerSmoothOpenImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_oriented_grassmann_smooth_submanifold]:
    the full smooth manifold and dimension assertion for
    Go(n,m) in Federer 3.2.28(2), pp. 264–265.
    The ambient inner product is the actual exterior product
    of 1.7.5, p. 32; one set of charts has every
    finite class. Positive degree retains both orientations. *)
Theorem euclidean_oriented_grassmann_smooth_submanifold (R:realType) m n:
  (0<m)%N ->(m<=n)%N ->
  is_inner_smooth_submanifold
    (@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m)
    (m*(n-m))%N
    [set x|simple x /\exterior_norm (euclidean_two_nonzero R)
      (@euclidean_inner_productP R n) x= 1].
Proof.
move=>hm hmn.
pose X:=Hom (R_n R m) (R_n R n).
pose Y:=exterior_power (R_n R n) m.
pose h2:=euclidean_two_nonzero R.
pose BX:=@euclidean_hom_inner_product R m n.
pose hBX:=@euclidean_hom_inner_productP R m n.
pose CY:=@exterior_inner_form R h2 (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) m.
pose hCY:=@exterior_inner_productP R h2 (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) m.
pose S:set X:=[set g|is_orthogonal_map (@euclidean_inner_product R m)
  (@euclidean_inner_product R n) (hom_as_linear g)].
pose Q:=@euclidean_exterior_word_map R m n.
pose d:=(m*(2*n-m-1)%/2)%N.
have hbY:=finite_ordinal_basis (@finite_e_lambda_basis R n (R_n R n)
  (@coordinate_basis R n) (@coordinate_basisP R n) h2 m).
have [e [p hChart]]:=finite_inner_chart_exists hCY hbY.
have [D [hD hDe]]:=@euclidean_exterior_word_class_one_field_exists R m n h2.
have hRank g (hg:S g) (J:Hom (R_n R d) X)
    (hJ:norm_tangent_cone (inner_norm hBX) S g=range J):
    has_linear_rank (hom_comp (D g) J) (m*(n-m)).
  pose T:=euclidean_stiefel_tangent_subspace g.
  pose LT:=hom_comp (D g) (hom_of_linear (subspace_inclusion T)).
  have hLT:has_linear_rank LT (m*(n-m)):=
    @euclidean_exterior_tangent_rank R m n h2 g (D g) hmn hg (hDe g).
  have hTan:norm_tangent_cone (inner_norm hBX) S g=[set h|T h].
    rewrite (@euclidean_stiefel_tangent R m n g hg).
    apply/seteqP; split=>h.
    - move=>hh; change (euclidean_gram_differential g h=0).
      by rewrite euclidean_gram_differentialE.
    - change (euclidean_gram_differential g h=0 ->
        hom_comp (euclidean_rectangular_adjoint h) g+
        hom_comp (euclidean_rectangular_adjoint g) h=0).
      by rewrite euclidean_gram_differentialE.
  apply:(@linear_same_image_rank R (subspace_space T) (R_n R d) Y
    LT (hom_comp (D g) J) _ _ hbY (m*(n-m)) hLT).
  - move=>t.
    have ht:norm_tangent_cone (inner_norm hBX) S g (subspace_val t).
      rewrite hTan; exact:subspace_valP t.
    rewrite hJ in ht; have [z _ hz]:=ht.
    exists z; change (D g (J z)=D g (subspace_val t)).
    by rewrite hz.
  - move=>z.
    have ht:T (J z).
      have hi:(range J) (J z) by exists z.
      by rewrite -hJ hTan in hi.
    exists (@subspace_lift R X T (J z) ht); reflexivity.
have hImage:=@finite_inner_smooth_open_constant_rank_image R X Y BX CY hBX hCY
  d (m*(n-m)) S Q D _ e p hChart
  (@euclidean_stiefel_smooth_submanifold R m n)
  (@euclidean_exterior_word_smooth R m n h2) hD hRank
  (@euclidean_exterior_word_relative_open R m n hm hmn).
by rewrite (@euclidean_exterior_word_image_simple_unit R m n hm) in hImage.
Qed.
