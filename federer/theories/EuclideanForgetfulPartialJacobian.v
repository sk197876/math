(** Federer (1969), 3.2.28(3), p. 266:
    the actual forgetful tangent Jacobian in the exact
    partial Euclidean graph needed by rectifiable coarea.
    The Hilbert Hom metric and original tangent are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerProductRestriction InnerNorm HilbertFormCompactness OrthogonalMaps EuclideanHomInnerCharts
  EuclideanRectangularAdjoint EuclideanGramDifferentialAlgebra EuclideanStiefelSubspaces EuclideanStiefelTangent
  EuclideanStiefelAdaptedBasis EuclideanFrameRestriction EuclideanForgetfulTangentJacobian
  FiniteInnerChartUP FiniteInnerDifferentialChart FiniteInnerTangentPartialJacobian
  TangentConeUP NormDifferentialUP PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialExteriorNormUP ExteriorIsometricPostcomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_forgetful_partial_jacobian]: the
    actual full differential and intrinsic tangent graph
    have the computed coarea Jacobian, Federer
    3.2.28(3), p. 266. All auxiliary
    bases, complement choices and diagonal coefficients
    have been discharged by the tangent theorem. *)
Theorem euclidean_forgetful_partial_jacobian (R:realType) k n N K
    (alpha:Hom (R_n R k) (R_n R k.+1))
    (e:Hom (R_n R N) (Hom (R_n R k.+1) (R_n R n)))
    (p:Hom (Hom (R_n R k.+1) (R_n R n)) (R_n R N))
    (t:Hom (Hom (R_n R k) (R_n R n)) (R_n R K))
    (g:Hom (R_n R k.+1) (R_n R n)):
  (k.+1<=n)%N ->is_finite_inner_chart (@euclidean_hom_inner_product R k.+1 n) e p ->
  is_orthogonal_map (@euclidean_hom_inner_product R k n) (@euclidean_inner_product R K) (hom_as_linear t) ->
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1) (hom_as_linear alpha) ->
  is_orthogonal_map (@euclidean_inner_product R k.+1) (@euclidean_inner_product R n) (hom_as_linear g) ->
  let O:=[set f:Hom (R_n R k.+1) (R_n R n)|is_orthogonal_map (@euclidean_inner_product R k.+1)
    (@euclidean_inner_product R n) (hom_as_linear f)] in
  let D:=@euclidean_frame_restriction R k k.+1 n alpha in
  has_norm_differential (inner_norm (@euclidean_inner_productP R N))
    (inner_norm (@euclidean_inner_productP R K)) (fun _=>True)
    (fun z=>t (hom_comp (e z) alpha)) (p g) (hom_comp t (hom_comp D e)) /\
  is_partial_exterior_norm (k*(2*n-k-1)%/2)
    (partial_function_source_restrict
      (norm_tangent_cone (inner_norm (@euclidean_inner_productP R N)) (p @` O) (p g))
      (partial_function_total (hom_comp t (hom_comp D e)))) ((Num.sqrt (2:R))^-k).
Proof.
move=>hkn hChart hT hAlpha hG O D.
pose X:=Hom (R_n R k.+1) (R_n R n).
pose Y:=Hom (R_n R k) (R_n R n).
pose hX:=@euclidean_hom_inner_productP R k.+1 n.
pose hY:=@euclidean_hom_inner_productP R k n.
pose TS:=euclidean_stiefel_tangent_subspace g.
pose TT:=euclidean_stiefel_tangent_subspace (hom_comp g alpha).
pose hTS:=restricted_inner_productP hX TS.
pose hTT:=restricted_inner_productP hY TT.
pose q:=(k*(2*n-k-1)%/2)%N.
have hDiff:=@euclidean_frame_restriction_differential R k k.+1 n alpha g.
split.
- exact:(@finite_inner_differential_chart R X Y _ _ hX hY N K e p t
    (@euclidean_frame_restriction R k k.+1 n alpha) g D hChart hT hDiff).
- have [S [hS hNorm]]:=@euclidean_forgetful_tangent_jacobian R k n alpha g hkn hAlpha hG.
  have hIncl:is_orthogonal_map (@restricted_inner_product R Y (@euclidean_hom_inner_product R k n) TT)
      (@euclidean_hom_inner_product R k n) (subspace_inclusion TT) by move=>x y.
  have hEval u:hom_as_linear (hom_comp D (hom_of_linear (subspace_inclusion TS))) u=
      subspace_inclusion TT (S u).
    change (hom_comp (subspace_val u) alpha=subspace_val (S u)); symmetry; exact:hS.
  have hAmbient:=@exterior_isometric_postcomposition_norm R (euclidean_two_nonzero R)
    (subspace_space TS) (subspace_space TT) Y _ _ _ hTS hTT hY
    (hom_as_linear S) (subspace_inclusion TT)
    (hom_as_linear (hom_comp D (hom_of_linear (subspace_inclusion TS)))) q
    ((Num.sqrt (2:R))^-k) hIncl hEval hNorm.
  have hTan:norm_tangent_cone (inner_norm hX) O g=(TS:set X).
    rewrite (@euclidean_stiefel_tangent R k.+1 n g hG).
    apply/seteqP; split=>h.
    + change (hom_comp (euclidean_rectangular_adjoint h) g+
        hom_comp (euclidean_rectangular_adjoint g) h=0 ->euclidean_gram_differential g h=0).
      by rewrite euclidean_gram_differentialE.
    + change (euclidean_gram_differential g h=0 ->hom_comp (euclidean_rectangular_adjoint h) g+
        hom_comp (euclidean_rectangular_adjoint g) h=0).
      by rewrite euclidean_gram_differentialE.
  have [b hb]:=euclidean_stiefel_tangent_dimension hG.
  exact:(@finite_inner_tangent_partial_jacobian_chart R X Y _ _ hX hY N K e p t O g TS
    (k.+1*(2*n-k.+1-1)%/2) b hb D q ((Num.sqrt (2:R))^-k) hChart hT hTan hAmbient).
Qed.
