(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: the ideal case of Artin–Rees. The actual
    Rees ring is Noetherian by the project's Hilbert
    proof. Its actual coefficient ideal has finite
    generators; a proved common support bound and exact
    coefficient comparison establish eventual equality.
    Source: Bourbaki, Commutative Algebra (1972),
    Chapter III, section 3, no. 1, Corollary 1, p. 197. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealIntersection
  CommutativePolynomialUP CommutativePolynomialSealed
  CommutativeSubringRealisationSealed
  CommutativeIdealProductSealed CommutativeIdealProductLaws
  CommutativeIdealPowersSealed CommutativeIdealPowersLaws
  ReesSubringSealed ReesSubringLaws ReesRingNoetherian
  ReesCoefficientIdeal FinitePolynomialImageSupport ReesIdealDegreeReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ideal_artin_rees]: the original
    eventual filtered-ideal equality, the ideal instance
    of Bourbaki (1972), Chapter III, section 3,
    no. 1, Corollary 1, p. 197. This supports
    the expanded ideal-closedness proof for 3.4.8(5), p. 328.
    No stabilization index, Rees generators or equality
    conclusion is assumed. *)
Theorem ideal_artin_rees (A:comNzRingType) (I J:set A):
  is_noetherian_commutative_ring A ->is_commutative_ideal I ->is_commutative_ideal J ->
  exists N,forall n,(N<=n)%N ->
    @CommutativeIdealProduct.value A I (J `&` @CommutativeIdealPowers.value A I n)=
      J `&` @CommutativeIdealPowers.value A I n.+1.
Proof.
move=>hNoetherian hI hJ.
pose B:=CommutativePolynomial.space A.
pose embed:=CommutativePolynomial.embed A.
pose variable:=CommutativePolynomial.variable A.
pose coefficient:=@CommutativePolynomial.coefficient A.
have hP:=CommutativePolynomial.laws A.
pose S:=@ReesSubring.value A B coefficient I.
pose hS:=@rees_subring_is_subring A B embed variable coefficient hP I.
pose C:=@CommutativeSubringRealisation.space B S hS.
pose inclusion:=@CommutativeSubringRealisation.inclusion B S hS.
have hC:=@CommutativeSubringRealisation.laws B S hS.
have hNoetherianC:=@rees_ring_noetherian A B C embed variable coefficient hP I inclusion hC hNoetherian hI.
pose U:set C:=fun c=>forall k,J (coefficient (inclusion c) k).
have hU:is_commutative_ideal U:=@polynomial_coefficient_ideal_preimage A B C embed variable coefficient hP inclusion J hJ.
have [F hF]:=hNoetherianC U hU.
have [N hSupport]:=@finite_polynomial_image_common_support A B C embed variable coefficient hP inclusion F.
exists N=>n hN;apply/seteqP;split.
- have hTarget:=@commutative_ideal_intersection A J
    (@CommutativeIdealPowers.value A I n.+1) hJ (@commutative_ideal_power_is_ideal A I n.+1).
  apply:commutative_ideal_product_minimal;first exact:hTarget.
  move=>a b ha [hb hPowerB];split.
  + exact:(@commutative_ideal_mul A J hJ a b hb).
  + have hPowerA:@CommutativeIdealPowers.value A I 1%N a.
      by rewrite (@commutative_ideal_power_oneE A I hI).
    have hProduct:=@commutative_ideal_power_multiply_members A I 1%N n a b hPowerA hPowerB.
    by rewrite add1n in hProduct.
- exact:(@rees_ideal_degree_reduction A B C embed variable coefficient hP I J hJ
    inclusion hC F N hF hSupport n hN).
Qed.
