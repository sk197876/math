(** Federer (1969), 3.4.8(2), p. 326:
    the original orthogonal germ homomorphism is invertible.
    Actual orthogonal-group inversion and every original
    representative give both germ inverse equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology OrthogonalGroupHaarMeasure AnalyticGermUP AnalyticGermRing
  PointedAnalyticPullbackRetraction AnalyticOrthogonalPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [analytic_orthogonal_germ_inverse_exists]: the
    original O_0(g) has the actual inverse O_0(g inverse),
    supporting the rotated ideal in 3.4.8(2), p. 326.
    All group operations remain local existence witnesses. *)
Theorem analytic_orthogonal_germ_inverse_exists (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (g:@orthogonal_group R X B hB n e he):
  exists h:@orthogonal_group R X B hB n e he,
    (forall alpha,@analytic_orthogonal_germ_map R X B hB n e he h
      (@analytic_orthogonal_germ_map R X B hB n e he g alpha)=alpha) /\
    (forall alpha,@analytic_orthogonal_germ_map R X B hB n e he g
      (@analytic_orthogonal_germ_map R X B hB n e he h alpha)=alpha).
Proof.
have [mulS [invS [eS hS]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
have [hLeft hRight]:=@orthogonal_element_inv R X B hB n e he mulS invS eS hS g.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose u:=@orthogonal_element_map R X B hB n e he g.
pose v:=@orthogonal_element_map R X B hB n e he (invS g).
pose P:=@analytic_orthogonal_germ_map R X B hB n e he g.
pose Q:=@analytic_orthogonal_germ_map R X B hB n e he (invS g).
have hP:=@analytic_orthogonal_germ_map_specification R X B hB n e he g.
have hQ:=@analytic_orthogonal_germ_map_specification R X B hB n e he (invS g).
exists (invS g);split.
- exact:(@pointed_analytic_germ_pullback_retraction R X X NX NX hNX hNX 0 0 u v P Q hP hQ hRight).
- exact:(@pointed_analytic_germ_pullback_retraction R X X NX NX hNX hNX 0 0 v u Q P hQ hP hLeft).
Qed.
