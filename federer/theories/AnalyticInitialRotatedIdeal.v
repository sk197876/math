(** Federer (1969), 3.4.11, p. 338:
    an actual leading polynomial of a rotated original
    ideal belongs to the rotated leading ideal. Actual
    orthogonal inverses and the already proved linear
    initial-polynomial transport supply the missing connection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology OrthogonalGroupHaarMeasure AnalyticGermUP AnalyticGermRing
  AnalyticRotatedGermIdeal AnalyticOrthogonalPullback AnalyticOrthogonalPullbackInverse
  AnalyticInitialPolynomialGermUP PointedInitialPolynomialGerm AnalyticInitialIdealSealed
  AnalyticInitialIdealLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_initial_rotated_ideal_member]:
    leading homogeneous polynomials commute with the original
    orthogonal substitutions in 3.4.11, p. 338.
    No equality of constructed ideals or choice of
    polynomial representatives is assumed. *)
Theorem analytic_initial_rotated_ideal_member (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
  (g:@orthogonal_group R X B hB n e he) alpha beta:
  @analytic_rotated_germ_ideal R X B hB n e he I g alpha ->
  is_initial_polynomial_germ alpha beta ->
  @analytic_rotated_germ_ideal R X B hB n e he
    (@AnalyticInitialIdeal.value R X (inner_norm hB) (inner_norm_real_norm hB) I) g beta.
Proof.
move=>hRotated hInitial.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose M:=fun g:@orthogonal_group R X B hB n e he=>
  @analytic_orthogonal_germ_map R X B hB n e he g.
have [delta [hDelta hAction]]:=(analytic_rotated_germ_ideal_membership I g alpha).1 hRotated.
have [h [hLeft hRight]]:=@analytic_orthogonal_germ_inverse_exists R X B hB n e he g.
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
have [hMapLeft hMapRight]:=@orthogonal_element_inv R X B hB n e he mulO invO unitO hO h.
have hOnto y:exists x,@orthogonal_element_map R X B hB n e he h x=y.
  exists (@orthogonal_element_map R X B hB n e he (invO h) y);exact:hMapRight.
have hOriginal:=@pointed_initial_polynomial_germ R X X NX NX hNX hNX
  (@orthogonal_element_map R X B hB n e he h) (M h)
  (@analytic_orthogonal_germ_map_specification R X B hB n e he h) hOnto alpha beta hInitial.
have hSource:M h alpha=delta by rewrite -hAction hLeft.
rewrite hSource in hOriginal.
apply/(analytic_rotated_germ_ideal_membership _ g beta).
exists (M h beta);split;last exact:hRight.
exact:(@analytic_initial_ideal_contains R X NX hNX I delta (M h beta) hDelta hOriginal).
Qed.
