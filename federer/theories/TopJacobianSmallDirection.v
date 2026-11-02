(** Federer (1969), 3.2.11, p. 249: the
    small singular-direction bound for the perturbed Jacobian.
    This supporting source-top estimate uses the unit-volume
    law of 1.7.6 and the product inequality of 1.7.5. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps EuclideanLinearJacobian CoordinateProjection InnerNorm InnerNormalization
  InnerProductUP OrthonormalFamilies EuclideanNormalChart OrthogonalMaps
  ExteriorGrading ExteriorMaps ExteriorNorm ExteriorOperatorNorm ExteriorOperatorEstimate
  ExteriorHadamardBound TopExteriorNorm FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_top_jacobian_small_direction]: the
    estimate J_n g <= epsilon (Lip f+epsilon)^(n-1)
    in Federer 3.2.11, p. 249. Supporting linear
    form: one unit direction has image length at most e,
    all directions have bound C, and the top-source
    Jacobian is at most e C^n in source dimension n+1. *)
Theorem euclidean_top_jacobian_small_direction (R:realType) n m
    (A:Hom (R_n R n.+1) (R_n R m)) (b:R_n R n.+1) e C:
  euclidean_inner_product b b= 1 ->0<=e ->0<=C ->
  inner_norm (@euclidean_inner_productP R m) (A b)<=e ->
  (forall x,inner_norm (@euclidean_inner_productP R m) (A x)<=
    C*inner_norm (@euclidean_inner_productP R n.+1) x) ->
  euclidean_linear_jacobian n.+1 A<=e*C^+n.
Proof.
move=>hb he hC hSmall hBound.
pose h2:=euclidean_two_nonzero R.
pose hX:=@euclidean_inner_productP R n.+1.
pose hY:=@euclidean_inner_productP R m.
pose O:=euclidean_normal_chart_forward ord0 hb.
have hO:is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) O:=euclidean_normal_chart_orthogonal ord0 hb.
pose a:=fun i:'I_n.+1=>O (@coordinate_basis R n.+1 i).
have ha:orthonormal_family (@euclidean_inner_product R n.+1) a.
  move=>i j; rewrite /a hO euclidean_inner_basis /coordinate_basis ffunE eq_sym.
  by [].
pose w:=e_lambda a (ord_tuple n.+1).
have hw:exterior_norm h2 hX w= 1:=orthonormal_product_unit_norm h2 hX ha.
have hJac:euclidean_linear_jacobian n.+1 A=
    exterior_norm h2 hY (exterior_power_map (hom_as_linear A) n.+1 w).
  exact (@top_exterior_operator_unit_value R h2 (R_n R n.+1) (R_n R m)
    (@euclidean_inner_product R n.+1) (@euclidean_inner_product R m)
    hX hY n.+1 (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1)
    (hom_as_linear A) w hw).
rewrite hJac /w exterior_map_indexed_product.
apply:le_trans (exterior_product_norm_bound h2 hY _) _.
rewrite big_ord_recl.
have hHead:inner_norm hY (A (a ord0))<=e.
  rewrite /a /O euclidean_normal_chart_axis; exact hSmall.
have hTail:(\prod_(i:'I_n) inner_norm hY (A (a (lift ord0 i))))<=C^+n.
  have hConst:(\prod_(i:'I_n) C)=C^+n by rewrite prodr_const card_ord.
  rewrite -hConst; apply:ler_prod=>i _; apply/andP; split; first exact:inner_norm_nonnegative.
  have hUnit:inner_norm hX (a (lift ord0 i))= 1:=orthonormal_norm1 hX ha _.
  by have h:=hBound (a (lift ord0 i)); rewrite hUnit mulr1 in h.
apply:le_trans (ler_wpM2r _ hHead) _.
- apply:prodr_ge0=>i _; exact:inner_norm_nonnegative.
- exact (ler_wpM2l he hTail).
Qed.
