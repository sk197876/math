(** Federer (1969), 3.2.48, pp. 285–286: the
    vertical subtraction block on Tan(I,1) times itself
    has top Jacobian sqrt(2)^mu. Supporting use of
    1.7.11, p. 36, via an actual orthogonal quotient. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom TensorUP InnerProductUP InnerProductLaws
  InnerNorm Bilinear ProductInner ProductInnerNormBounds ProductInnerDifferential
  ProductFiniteBasis LinearBasis OrthogonalMaps AdjointUP ExteriorGrading
  ExteriorMaps ExteriorNorm ExteriorOperatorNorm OperatorNormUP
  InnerExteriorPositivity ScaledOrthogonalQuotientExteriorNorm
  EuclideanStiefelHalfNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [cartesian_difference_hom]: the actual subtraction
    l_1 in 3.2.48, p. 285, expressed by the
    two Cartesian projections of 1.7.11, p. 36. *)
Definition cartesian_difference_hom (R:realType) (V:lmodType R):=
  @product_first_projection_hom R V V-@product_second_projection_hom R V V.

(** Source for [cartesian_difference_homE]: supporting exact values
    of l_1 in 3.2.48, pp. 285–286: the two
    original vectors are subtracted, without an auxiliary representative. *)
Lemma cartesian_difference_homE (R:realType) (V:lmodType R) (z:V*V):
  @cartesian_difference_hom R V z=z.1-z.2.
Proof. by []. Qed.

(** Source for [cartesian_difference_top_exterior_norm]: the exact
    vertical factor sqrt(2)^mu in 3.2.48, p. 286.
    The normalized antidiagonal is an actual isometric section,
    and its adjoint is the corresponding normalized subtraction.
    The original finite inner space and degree zero remain. *)
Theorem cartesian_difference_top_exterior_norm (R:realType) (h2:(1+1:R)!=0)
    (V:lmodType R) B (hB:@is_inner_product R V B) q (b:'I_q->V) (hb:is_basis b):
  exterior_operator_norm h2 (product_inner_productP hB hB) hB
    (cartesian_basisP hb hb) (hom_as_linear (@cartesian_difference_hom R V)) q=
    (Num.sqrt (2:R))^+q.
Proof.
pose P:lmodType R:=[the lmodType R of (V*V)%type].
pose hP:=product_inner_productP hB hB.
pose s:=(Num.sqrt (2:R))^-1.
pose identity:Hom V V:=hom_of_linear (linear_id V).
pose H:{linear V->P}:=hom_as_linear (product_pair_hom (s*:identity) ((-s)*:identity)).
pose F:{linear P->V}:=hom_as_linear (@cartesian_difference_hom R V).
pose Q:{linear P->V}:=hom_as_linear (s*:@cartesian_difference_hom R V).
have hHValue x:H x=(s*:x,(-s)*:x).
  by rewrite /H hom_as_linearE product_pair_homE !hom_scaleE.
have hQValue x:Q x=s*:(x.1-x.2).
  by rewrite /Q hom_as_linearE hom_scaleE cartesian_difference_homE.
have [hPositive hCoefficient]:=euclidean_stiefel_half_normalization R.
change (is_true (0<s)) in hPositive.
change (2*s*s= 1) in hCoefficient.
have hOrthogonal:is_orthogonal_map B (product_inner hB hB) H.
  move=>x y; rewrite !hHValue product_innerE
    !(bilZl (inner_bilinear hB)) !(bilZr (inner_bilinear hB)).
  have hFactor:s*(s*B x y)+(-s)*((-s)*B x y)=(2*s*s)*B x y by ring.
  by rewrite hFactor hCoefficient mul1r.
have hAdjoint:is_adjoint B (product_inner hB hB) H Q.
  move=>x y; rewrite hHValue hQValue product_innerE
    !(bilZl (inner_bilinear hB)) !(bilZr (inner_bilinear hB))
    (bilBr (inner_bilinear hB)).
  change (s*(B x y.1-B x y.2)=s*B x y.1+(-s)*B x y.2).
  ring.
have hIdentity:is_orthogonal_map B B (linear_id V) by move=>x y.
have hRoot:0<Num.sqrt (2:R) by rewrite sqrtr_gt0 ltr0n.
have hFactor x:F x=Num.sqrt (2:R)*:(linear_id V (Q x)).
  rewrite hQValue scalerA /s mulfV ?gt_eqF // scale1r.
  exact:cartesian_difference_homE.
have hNorm:=@scaled_orthogonal_quotient_top_exterior_norm R h2 V P V B _ B hB hP hB
  q b hb H Q (linear_id V) F (Num.sqrt (2:R)) hOrthogonal hAdjoint hIdentity
  (ltW hRoot) hFactor.
exact (operator_norm_unique (exterior_operator_normP h2 hP hB (cartesian_basisP hb hb) F q) hNorm).
Qed.
