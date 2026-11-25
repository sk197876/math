(** Federer (1969), 3.2.28, pp. 265–267:
    the actual tangent exterior norm equals the norm
    of the exact partial differential graph in
    Euclidean ambient coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerProductRestriction InnerNorm OrthogonalMaps LinearBasis FiniteInnerChartUP
  TangentConeUP PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  InnerExteriorPositivity ExteriorMaps OperatorNormUP PartialExteriorNormUP
  FiniteInnerPartialExteriorChart FiniteInnerTangentGraphChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_tangent_partial_jacobian_chart]:
    the tangent/partial-graph Jacobian equality required
    when applying 3.2.20 and 3.2.22 in Federer
    3.2.28, pp. 265–267. The actual tangent
    and its basis-size laws are proved separately;
    no partial value outside that tangent is introduced. *)
Theorem finite_inner_tangent_partial_jacobian_chart (R:realType) (X Y:lmodType R)
    (B:X->X->R) (C:Y->Y->R) (hB:is_inner_product B) (hC:is_inner_product C)
    n k (e:Hom (R_n R n) X) (p:Hom X (R_n R n)) (t:Hom Y (R_n R k))
    (S:set X) a (T:subspace X) d (b:'I_d->subspace_space T) (hb:is_basis b)
    (L:Hom X Y) q j:
  is_finite_inner_chart B e p ->
  is_orthogonal_map C (@euclidean_inner_product R k) (hom_as_linear t) ->
  norm_tangent_cone (inner_norm hB) S a=(T:set X) ->
  is_operator_norm (exterior_inner_productP (euclidean_two_nonzero R)
      (restricted_inner_productP hB T) q)
    (exterior_inner_productP (euclidean_two_nonzero R) hC q)
    (exterior_power_map (hom_as_linear (hom_comp L (hom_of_linear (subspace_inclusion T)))) q) j ->
  is_partial_exterior_norm q
    (partial_function_source_restrict
      (norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) (p @` S) (p a))
      (partial_function_total (hom_comp t (hom_comp L e)))) j.
Proof.
move=>hChart hT hTan hNorm.
pose U:=subspace_space T.
pose BT:=@restricted_inner_product R X B T.
pose hBT:=restricted_inner_productP hB T.
pose A:=hom_comp p (hom_of_linear (subspace_inclusion T)).
pose F:=hom_comp L (hom_of_linear (subspace_inclusion T)).
have hA:is_orthogonal_map BT (@euclidean_inner_product R n) (hom_as_linear A).
  move=>x y.
  change (euclidean_inner_product (p (subspace_val x)) (p (subspace_val y))=
    B (subspace_val x) (subspace_val y)).
  exact:(@finite_inner_chart_inverse_product R X B n e p hChart (subspace_val x) (subspace_val y)).
apply:(@finite_inner_partial_exterior_chart R U Y BT C hBT hC d b hb n k q A t F _ j hA hT).
- move=>v w; exact:(@finite_inner_tangent_partial_graph_chart R X Y B hB n k e p t S a T L hChart hTan v w).
- exact hNorm.
Qed.
