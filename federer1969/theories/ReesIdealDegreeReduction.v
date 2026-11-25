(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: finite generators of the actual filtered
    Rees ideal give the Artin–Rees inclusion by comparing
    one original coefficient. Every multiplier and coefficient
    is taken from the actual ring inclusion.
    Source: Bourbaki, Commutative Algebra (1972),
    Chapter III, section 3, no. 1, Corollary 1, p. 197. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativePolynomialUP CommutativePolynomialBasicLaws
  CommutativePolynomialFiniteSums CommutativeSubringRealisationUP
  CommutativeIdealProductSealed CommutativeIdealProductLaws
  CommutativeIdealPowersSealed CommutativeIdealPowersLaws
  ReesSubringUP ReesSubringSealed ReesMonomialLift AdicIdealProductStep FiniteIdealCoefficientImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rees_ideal_degree_reduction]: the finite
    Rees-ideal coefficient comparison proves the original
    filtered inclusion in Artin–Rees, as in the cited
    Corollary 1. Finite generators and their support
    bounds are discharged by the final Noetherian theorem. *)
Theorem rees_ideal_degree_reduction (A B C:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (I J:set A) (hJ:is_commutative_ideal J) (inclusion:{rmorphism C->B})
    (hC:is_commutative_subring_realisation (@ReesSubring.value A B coefficient I) inclusion)
    (F:seq C) N:
  is_generated_commutative_ideal [set c:C|c \in F]
    [set c:C|forall k,J (coefficient (inclusion c) k)] ->
  (forall (i:'I_(size F)) k,(N<=k)%N ->coefficient (inclusion (nth 0 F i)) k = 0) ->
  forall n,(N<=n)%N ->
    (J `&` @CommutativeIdealPowers.value A I n.+1) `<=`
      @CommutativeIdealProduct.value A I (J `&` @CommutativeIdealPowers.value A I n).
Proof.
move=>hF hSupport n hNn x [hJx hPowerX].
pose power:=@CommutativeIdealPowers.value A I.
pose T:=@CommutativeIdealProduct.value A I (J `&` power n).
have hT:is_commutative_ideal T:=commutative_ideal_product_is_ideal _ _.
have [z [hZValue hZIdeal]]:=@rees_monomial_lift_exists A B C embed variable coefficient hP
  I J hJ inclusion hC n.+1 x hPowerX hJx.
have [multipliers hRepresentation]:=(@finite_ideal_coefficient_image C
  [set c:C|forall k,J (coefficient (inclusion c) k)] F hF z).1 hZIdeal.
have hEquation:=congr1 (fun c:C=>coefficient (inclusion c) n.+1) hRepresentation.
rewrite hZValue (@polynomial_monomial_coefficient A B embed variable coefficient hP) eqxx in hEquation.
rewrite rmorph_sum (@polynomial_coefficient_sum A B embed variable coefficient hP) in hEquation.
have hExpansion:x = \sum_(i<size F) \sum_(j<n.+2)
    coefficient (inclusion (multipliers i)) j*
      coefficient (inclusion (nth 0 F i)) (n.+1-j)%N.
  rewrite hEquation;apply:eq_bigr=>i _.
  by rewrite rmorphM (@polynomial_coefficient_multiply A B embed variable coefficient hP).
have hRingCoefficient (c:C) k:power k (coefficient (inclusion c) k).
  have hMember:@ReesSubring.value A B coefficient I (inclusion c).
    apply:(@commutative_subring_inclusion_image B (@ReesSubring.value A B coefficient I)
      C inclusion hC (inclusion c)).2;by exists c.
  exact:(@ReesSubring.laws A B coefficient I (inclusion c)).1 hMember k.
rewrite hExpansion.
apply:(big_ind T);first exact:commutative_ideal_zero hT.
- move=>a b ha hb;exact:(@commutative_ideal_add A T hT a b ha hb).
- move=>i _;apply:(big_ind T);first exact:commutative_ideal_zero hT.
  + move=>a b ha hb;exact:(@commutative_ideal_add A T hT a b ha hb).
  + move=>j _.
    have hJBound:(j<=n.+1)%N:=ltn_ord j.
    case:(posnP (j:nat))=>[hZero|hPositive].
    * rewrite hZero subn0 (hSupport i n.+1 (leq_trans hNn (leqnSn n))) mulr0.
      exact:commutative_ideal_zero hT.
    * have hSuccessor:(j.-1).+1=(j:nat):=prednK hPositive.
      have hPredBound:(j.-1<=n)%N.
        by move:hJBound;rewrite -{1}hSuccessor.
      have hSubtract:(n.+1-j)%N=(n-j.-1)%N by rewrite -{1}hSuccessor subSS.
      have hExponent:(j.-1+(n.+1-j))%N=n by rewrite hSubtract (subnKC hPredBound).
      have hAPower:power (j.-1).+1 (coefficient (inclusion (multipliers i)) j).
        rewrite hSuccessor;exact:hRingCoefficient.
      have hBIn:J (coefficient (inclusion (nth 0 F i)) (n.+1-j)%N).
        have hGenerator:=@generated_commutative_ideal_contains C _ _ hF (nth 0 F i)
          (mem_nth 0 (ltn_ord i)).
        exact:hGenerator.
      have hStep:=@adic_ideal_product_step A I J hJ j.-1 (n.+1-j)%N
        (coefficient (inclusion (multipliers i)) j)
        (coefficient (inclusion (nth 0 F i)) (n.+1-j)%N)
        hAPower hBIn (hRingCoefficient (nth 0 F i) (n.+1-j)%N).
      by rewrite hExponent in hStep.
Qed.
