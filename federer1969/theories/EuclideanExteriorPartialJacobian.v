(** Federer (1969), 3.2.28(2), pp. 264–265:
    the actual Q differential has intrinsic tangent
    Jacobian one in the Euclidean coordinates used
    for the rectifiable coarea theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerNorm HilbertFormCompactness OrthogonalMaps EuclideanHomInnerCharts EuclideanRectangularAdjoint
  EuclideanGramDifferentialAlgebra EuclideanStiefelSubspaces EuclideanStiefelTangent EuclideanStiefelAdaptedBasis
  ExteriorGrading ExteriorNorm InnerExterior InnerExteriorPositivity EuclideanExteriorWordSmooth EuclideanExteriorWordDifferentialField
  EuclideanExteriorTangentJacobian FiniteInnerChartUP FiniteInnerDifferentialChart FiniteInnerTangentPartialJacobian
  TangentConeUP NormDifferentialUP NormClassOneUP PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction PartialExteriorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_exterior_partial_jacobian_one]:
    the full-domain differential and exact tangent partial
    exterior norm used for J Q=1 in Federer
    3.2.28(2), p. 265. Every auxiliary
    tangent basis and differential formula is discharged
    by the proved Stiefel and exterior calculus laws. *)
Theorem euclidean_exterior_partial_jacobian_one (R:realType) m n N K
    (e:Hom (R_n R N) (Hom (R_n R m) (R_n R n)))
    (p:Hom (Hom (R_n R m) (R_n R n)) (R_n R N))
    (t:Hom (exterior_power (R_n R n) m) (R_n R K))
    (g:Hom (R_n R m) (R_n R n)):
  (m<=n)%N ->is_finite_inner_chart (@euclidean_hom_inner_product R m n) e p ->
  is_orthogonal_map
    (@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m)
    (@euclidean_inner_product R K) (hom_as_linear t) ->
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear g) ->
  let O:=[set f:Hom (R_n R m) (R_n R n)|is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear f)] in
  exists L:Hom (Hom (R_n R m) (R_n R n)) (exterior_power (R_n R n) m),
    has_norm_differential (inner_norm (@euclidean_hom_inner_productP R m n))
      (@exterior_norm R (euclidean_two_nonzero R) (R_n R n) (@euclidean_inner_product R n)
        (@euclidean_inner_productP R n) m)
      (fun _=>True) (@euclidean_exterior_word_map R m n) g L /\
    has_norm_differential (inner_norm (@euclidean_inner_productP R N))
      (inner_norm (@euclidean_inner_productP R K)) (fun _=>True)
      (fun z=>t (euclidean_exterior_word_map (e z))) (p g) (hom_comp t (hom_comp L e)) /\
    is_partial_exterior_norm (m*(n-m))
      (partial_function_source_restrict
        (norm_tangent_cone (inner_norm (@euclidean_inner_productP R N)) (p @` O) (p g))
        (partial_function_total (hom_comp t (hom_comp L e)))) 1.
Proof.
move=>hmn hChart hT hG O.
pose X:=Hom (R_n R m) (R_n R n).
pose Y:=exterior_power (R_n R n) m.
pose hX:=@euclidean_hom_inner_productP R m n.
pose hY:=@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m.
have [D [hD hDE]]:=@euclidean_exterior_word_class_one_field_exists R m n (euclidean_two_nonzero R).
pose L:=D g.
have hDiff:has_norm_differential (inner_norm hX) (inner_norm hY) (fun _=>True)
    (@euclidean_exterior_word_map R m n) g L:=
    @norm_class_one_differential R X Y (inner_norm hX) (inner_norm hY)
      (fun _=>True) (@euclidean_exterior_word_map R m n) D hD g I.
exists L; split; first exact hDiff.
split.
- exact:(@finite_inner_differential_chart R X Y _ _ hX hY N K e p t
    (@euclidean_exterior_word_map R m n) g L hChart hT hDiff).
- pose T:=euclidean_stiefel_tangent_subspace g.
  have hTan:norm_tangent_cone (inner_norm hX) O g=(T:set X).
    rewrite (@euclidean_stiefel_tangent R m n g hG).
    apply/seteqP; split=>h; change ((hom_comp (euclidean_rectangular_adjoint h) g+
      hom_comp (euclidean_rectangular_adjoint g) h=0)->euclidean_gram_differential g h=0) ||
      change (euclidean_gram_differential g h=0 ->hom_comp (euclidean_rectangular_adjoint h) g+
        hom_comp (euclidean_rectangular_adjoint g) h=0);
      by rewrite euclidean_gram_differentialE.
  have [b hb]:=euclidean_stiefel_tangent_dimension hG.
  apply:(@finite_inner_tangent_partial_jacobian_chart R X Y _ _ hX hY N K e p t O g T
    (m*(2*n-m-1)%/2) b hb L (m*(n-m)) 1 hChart hT hTan).
  exact:(@euclidean_exterior_tangent_jacobian_one R m n (euclidean_two_nonzero R) g L hmn hG (hDE g)).
Qed.
