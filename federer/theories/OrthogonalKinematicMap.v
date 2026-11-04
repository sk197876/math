(** Federer (1969), 3.2.48, pp. 284–285: the
    actual map Psi(x,y)=x y inverse on the orthogonal
    group. The ambient polynomial x y adjoint supplies a
    legitimate smooth extension; inversion is not extended artificially. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  LinearBasis HomCompositionDeterminant EuclideanInnerProduct InnerProductUP InnerProductLaws InnerNorm HilbertFormCompactness
  EuclideanHomInnerCharts EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  EuclideanGramDifferentialAlgebra OrthogonalMaps ProductInner ProductInnerNormBounds
  EuclideanHomCompositionBound EuclideanHomRegularity NormRegularity NormRegularityOperations NormRegularityLinearMaps
  NormDifferentialUP NormDifferentialLinear NormFiniteLinearBound
  NormDifferentialBilinearProduct NormBilinearDifferentialAlgebra NormOpenDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_kinematic_map]: the actual Psi
    of 3.2.48, p. 284. The adjoint equals the inverse
    on its original orthogonal domain; the same formula is
    a polynomial on the ambient Hilbert Hom product. *)
Definition orthogonal_kinematic_map (R:realType) N
    (z:Hom (R_n R N) (R_n R N)*Hom (R_n R N) (R_n R N)):=
  hom_comp z.1 (euclidean_rectangular_adjoint z.2).

(** Source for [orthogonal_kinematic_map_class]: actual smoothness
    of Psi, justified by the bilinear operation and inversion
    in 3.2.48, p. 285. The polynomial representative
    x y adjoint is of every finite class on the full ambient space. *)
Theorem orthogonal_kinematic_map_class (R:realType) N k:
  norm_class
    (inner_norm_real_norm (product_inner_productP
      (@euclidean_hom_inner_productP R N N) (@euclidean_hom_inner_productP R N N)))
    (inner_norm_real_norm (@euclidean_hom_inner_productP R N N))
    setT (@orthogonal_kinematic_map R N) k.
Proof.
pose H:=Hom (R_n R N) (R_n R N).
pose P:lmodType R:=[the lmodType R of (H*H)%type].
pose hH:=@euclidean_hom_inner_productP R N N.
pose hP:=product_inner_productP hH hH.
pose F:=@product_first_projection_hom R H H.
pose G:=@product_second_projection_hom R H H.
have hF:norm_bounded_linear (inner_norm hP) (inner_norm hH) F.
  exists 1; split; first exact:ler01.
  by move=>z; rewrite mul1r; exact (@product_inner_first_norm_bound R H H _ _ hH hH z).
have hG:norm_bounded_linear (inner_norm hP) (inner_norm hH) G.
  exists 1; split; first exact:ler01.
  by move=>z; rewrite mul1r; exact (@product_inner_second_norm_bound R H H _ _ hH hH z).
have hFirst:=@norm_class_linear R P H _ _ (inner_norm_real_norm hP)
  (inner_norm_real_norm hH) setT F k (fun z _=>norm_full_domain_interior _ z) hF.
have hSecond:=@norm_class_linear R P H _ _ (inner_norm_real_norm hP)
  (inner_norm_real_norm hH) setT G k (fun z _=>norm_full_domain_interior _ z) hG.
exact (@euclidean_hom_composition_norm_class R P _ (inner_norm_real_norm hP)
  N N N setT F (fun z=>euclidean_rectangular_adjoint (G z)) k hFirst
  (@euclidean_hom_adjoint_norm_class R P _ (inner_norm_real_norm hP) N N setT G k hSecond)).
Qed.

(** Source for [orthogonal_kinematic_map_differential]: the actual
    ambient differential u y adjoint + x v adjoint,
    supporting the first displayed differential in 3.2.48,
    p. 285. Its existence is proved from the actual
    product polynomial, not an independent derivative-field hypothesis. *)
Theorem orthogonal_kinematic_map_differential (R:realType) N
    (x y:Hom (R_n R N) (R_n R N)):
  exists D:Hom [the lmodType R of
      ((Hom (R_n R N) (R_n R N))*(Hom (R_n R N) (R_n R N)))%type]
      (Hom (R_n R N) (R_n R N)),
    has_norm_differential
      (inner_norm (product_inner_productP
        (@euclidean_hom_inner_productP R N N) (@euclidean_hom_inner_productP R N N)))
      (inner_norm (@euclidean_hom_inner_productP R N N))
      setT (@orthogonal_kinematic_map R N) (x,y) D /\
    forall u v,D (u,v)=hom_comp u (euclidean_rectangular_adjoint y)+
      hom_comp x (euclidean_rectangular_adjoint v).
Proof.
pose V:=R_n R N.
pose H:=Hom V V.
pose P:lmodType R:=[the lmodType R of (H*H)%type].
pose hH:=@euclidean_hom_inner_productP R N N.
pose hP:=product_inner_productP hH hH.
pose F:=@product_first_projection_hom R H H.
pose adj:Hom H H:=hom_of_linear (GRing.Linear.clone _ _ _ _ (@euclidean_rectangular_adjoint R N N) _).
pose G:=hom_comp adj (@product_second_projection_hom R H H).
have hF:norm_bounded_linear (inner_norm hP) (inner_norm hH) F.
  exists 1; split; first exact:ler01.
  by move=>z; rewrite mul1r; exact (@product_inner_first_norm_bound R H H _ _ hH hH z).
have hG:norm_bounded_linear (inner_norm hP) (inner_norm hH) G.
  pose b:=@hom_rank_one_base R V V N N (@coordinate_basis R N)
    (@coordinate_basisP R N) (@coordinate_basis R N).
  have hb:is_basis b:=@hom_rank_one_baseP R V V N N (@coordinate_basis R N)
    (@coordinate_basisP R N) (@coordinate_basis R N) (@coordinate_basisP R N).
  have [C [hC hBound]]:=@norm_finite_linear_bounded R H H _ _
    (inner_norm_real_norm hH) (inner_norm_real_norm hH) _ b hb adj.
  exists C; split; first exact hC.
  move=>z; apply:le_trans (hBound z.2) _.
  exact (ler_wpM2l hC (@product_inner_second_norm_bound R H H _ _ hH hH z)).
have hDF:=@norm_differential_linear R P H _ _ (inner_norm_real_norm hP)
  (inner_norm_real_norm hH) setT (x,y) F (norm_full_domain_interior _ (x,y)) hF.
have hDG:=@norm_differential_linear R P H _ _ (inner_norm_real_norm hP)
  (inner_norm_real_norm hH) setT (x,y) G (norm_full_domain_interior _ (x,y)) hG.
have [hB [C [hC hBound]]]:=@euclidean_composition_hilbert_bilinear R N N N.
exists (norm_bilinear_product_linear_term hB (F (x,y)) (G (x,y)) F G).
split.
- exact (@norm_differential_bilinear_product R P H H H _ _ _ _
    (inner_norm_real_norm hP) (inner_norm_real_norm hH) (inner_norm_real_norm hH)
    (inner_norm_real_norm hH) (@hom_comp R V V V) hB C setT F G (x,y) F G
    hC hBound hDF hDG).
- by move=>u v.
Qed.
