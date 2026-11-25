(** Federer (1969), 3.2.28(4), pp. 266–267:
    the actual two-to-one area identity on compact
    antipodal subsets of the given manifold. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom LinearBasis GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  SymmetricGrading InnerSymmetric InnerSymmetricPositivity SymmetricMonomialBasis FiniteOrdinalBasis
  FiniteInnerChart FiniteInnerSubmanifoldUP FiniteInnerSmoothCompactImage FiniteInnerCompactTangentArea
  SymmetricSquareGeometry SymmetricSquareSmooth SymmetricSquareTangentIsometry SymmetricSquareLipschitz
  SymmetricSquareFibreMultiplicity HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [inner_projective_square_compact_area]: the
    area identity of Federer 3.2.28(4), p. 267,
    on compact antipodal subsets of B. Such subsets
    need not themselves be manifolds. Their intrinsic
    approximate Jacobian is proved to be one almost
    everywhere, and every nonempty fibre has count two. *)
Theorem inner_projective_square_compact_area (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n (b:'I_n->V) (hb:is_basis b)
    mu k (S K:set V):
  (1<=k)%N ->is_inner_submanifold B mu k S ->K `<=` S ->
  @compact [the topologicalType of inner_metric_space hB] K ->
  (forall x,S x ->inner_norm hB x= 1%R) ->(forall x,K x ->K (-x)%R) ->
  @hausdorff_measure R (inner_metric_space hB) mu K=
    (2:R)%:E* @hausdorff_measure R (inner_metric_space (@symmetric_inner_productP R V B hB 2)) mu
      ((@inner_projective_square R V) @` K).
Proof.
Local Open Scope ring_scope.
move=>hk [N [e [p [hChart hS]]]] hKS hK hUnit hAnti.
pose Y:=symmetric_power V 2.
pose C:=@symmetric_inner_form R V B hB 2.
pose hC:=@symmetric_inner_productP R V B hB 2.
pose F:=@inner_projective_square R V.
have hbY:=finite_ordinal_basis (@symmetric_finite_monomial_basis R V n b hb 2).
have [a [t hTarget]]:=finite_inner_chart_exists hC hbY.
have hFK:@compact [the topologicalType of inner_metric_space hC] (F @` K).
  exact:(@inner_class_map_compact_image R V Y B C hB hC F 0 K
    (@inner_projective_square_smooth R V B hB 0%N) hK).
have hUnitK x:K x ->inner_norm hB x= 1%R by move=>hx; exact:hUnit x (hKS x hx).
have hValues x:K x ->exists D:Hom V Y,
    NormDifferentialUP.has_norm_differential (inner_norm hB) (inner_norm hC) (fun _=>True) F x D /\
    forall v w,TangentConeUP.norm_tangent_cone (inner_norm hB) S x v ->
      TangentConeUP.norm_tangent_cone (inner_norm hB) S x w ->C (D v) (D w)=B v w.
  move=>hx; exact:(@inner_projective_square_actual_tangent_isometry R V B hB S x hUnit (hUnitK x hx)).
apply:(@finite_inner_compact_tangent_area R V Y B C hB hC N _ mu k e p a t S K F (2:R)%:E
  hChart hTarget hk hS hKS hK hFK _ hValues).
- exists 1%R; exact:(@inner_projective_square_unit_lipschitz R V B hB K hUnitK).
- by rewrite lee_fin ler0n.
- move=>y hy; exact:(@inner_projective_square_fibre_count R V B hB K y hUnitK hAnti hy).
Qed.
