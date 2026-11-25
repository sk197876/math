(** Federer (1969), 4.1.14, p. 371: bound the
    actual exterior image of the normalized orientation by
    sigma^m. This is the all-degree exterior operator bound
    of 4.1.7, p. 359, with a point-dependent cap.
    Degree zero and zero derivative caps are included. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentCoefficientNorms CurrentSpaces CurrentIntegrationCriterion
  NormalisedCurrentSealed CurrentImageDensityPairing CurrentMapDifferential
  EuclideanHomOperator HomSpaceTopology CurrentExteriorOperatorMassBound
  OperatorNormUP OperatorNorm NormalisedDistributionRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_image_density_pointwise_majorant]:
    the original normalized image weight is bounded by
    the m-th power of any cap of the actual derivative,
    supporting Federer 4.1.14, p. 371. Positivity of
    the cap follows from the actual operator norm. *)
Theorem current_image_density_pointwise_majorant
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T)
    (f:R_n R n->R_n R nu) (x:current_domain R n U) (a:R):
  @euclidean_operator_norm R n nu
    (@current_map_differential R n nu U f (set_val x))<=a->
  @current_vector_mass R h2 nu m
    (@current_image_density R n nu m U f
      (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT) x)<=a^+m.
Proof.
move=>hCap.
pose D:=@current_map_differential R n nu U f (set_val x).
pose op:=@euclidean_operator_norm R n nu D.
have hOp:0<=op by exact:hom_operator_norm_nonnegative.
have hA:0<=a:=le_trans hOp hCap.
have hOperator:is_operator_norm (@euclidean_inner_productP R n)
    (@euclidean_inner_productP R nu) (hom_as_linear D) op.
  exact:(linear_operator_normP (@euclidean_inner_productP R n)
    (@euclidean_inner_productP R nu) (@coordinate_basisP R n) (hom_as_linear D)).
have hNormal:=@NormalisedCurrent.laws R h2 n m U hU T hT.
have hExterior:=@current_exterior_operator_mass_bound R h2 n nu
  (hom_as_linear D) op hOperator m
  (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT x).
have hUnit:=normalised_distribution_density_unit_bound hNormal x.
have hFirst:@current_vector_mass R h2 nu m
    (@current_image_density R n nu m U f
      (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT) x)<=op^+m.
  have h:=ler_wpM2l (exprn_ge0 m hOp) hUnit.
  rewrite mulr1 in h;exact:le_trans hExterior h.
have hPower:forall j:nat,op^+j<=a^+j.
  elim=>[|j ih];first by rewrite !expr0.
  rewrite !exprS.
  exact:(le_trans (ler_wpM2l hOp ih) (ler_wpM2r (exprn_ge0 j hA) hCap)).
exact:le_trans hFirst (hPower m).
Qed.
