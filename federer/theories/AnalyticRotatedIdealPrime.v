(** Federer (1969), 3.4.8(8), p. 329:
    the actual rotated prime ideal has a domain
    quotient. Transport primeness through the proved
    inverse of the original orthogonal pullback. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology AnalyticGermUP AnalyticGermRing CommutativeIdealUP
  AnalyticRotatedGermIdeal AnalyticOrthogonalPullback AnalyticOrthogonalPullbackInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_rotated_germ_ideal_prime]: the
    original prime ideal I remains prime after
    orthogonal pullback, as used for the domain
    O_0(R^n)/I_g in 3.4.8(8), p. 329.
    Reuse the actual inverse-membership, ideal-closure
    and properness theorems. *)
Theorem analytic_rotated_germ_ideal_prime (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
  (g:@orthogonal_group R X B hB n e he):
  is_prime_commutative_ideal I ->
    is_prime_commutative_ideal (@analytic_rotated_germ_ideal R X B hB n e he I g).
Proof.
move=>hPrime;split.
- exact:(@analytic_rotated_germ_ideal_is_ideal R X B hB n e he I g hPrime.1).
split.
- exact:(@analytic_rotated_germ_ideal_proper R X B hB n e he I g hPrime.2.1).
have [h [hLeft hRight]]:=@analytic_orthogonal_germ_inverse_exists R X B hB n e he g.
have hMember:=@analytic_rotated_germ_ideal_inverse_membership R X B hB n e he I g h hLeft hRight.
move=>alpha beta /hMember hProduct.
rewrite rmorphM in hProduct.
have [hAlpha|hBeta]:=hPrime.2.2 _ _ hProduct.
- left;exact:(hMember alpha).2 hAlpha.
- right;exact:(hMember beta).2 hBeta.
Qed.
