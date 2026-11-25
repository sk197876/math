(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8), p. 329:
    original holomorphic division identifies every quotient
    class with a finite polynomial in the selected
    coordinate. The established division proof is reused. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus HolomorphicLinear Hom RealNormUP NormDifferentialUP HolomorphicGermRepresentatives
  HolomorphicGermUP HolomorphicGermRing ComplexWeierstrassTransverseUP ComplexWeierstrassTransversePullback
  ComplexWeierstrassRegularUP ComplexWeierstrassDivisionUP ComplexWeierstrassDivisionWithTransverse
  HolomorphicPolynomialDivisionModel CommutativePolynomialUP CommutativePolynomialEvaluationUP
  CommutativeQuotientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section QuotientImage.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_complex_norm NX) (hNK:is_complex_norm NK).
Variable v:X.
Variable xi:Hom X (ComplexScalars.C R)^o.
Variables (inclusion:Hom K X) (projection:Hom X K).
Hypothesis hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0.
Hypothesis hXi:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi).
Hypothesis hXiValues:forall x,holomorphic_representative_value fXi x = xi x.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)].
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R K NK (complex_norm_real hNK) (projection 0))].
Local Notation E:=(@complex_weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(holomorphic_germ fXi:G).
Variable B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism B->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E Gamma J.

Variables (C:comNzRingType) (I:G->Prop) (pi:{rmorphism G->C}).
Hypothesis hQuotient:is_commutative_ideal_quotient I pi.

(** Source for [holomorphic_quotient_polynomial_representative]:
    the equality p(Q_j)=p(Q_(j-1))[zeta_j]
    in 3.4.8(8), p. 329. Actual division
    leaves a finite transverse polynomial with the
    same quotient image. Apply the existing holomorphic
    polynomial-division theorem of 3.4.7 directly. *)
Theorem holomorphic_quotient_polynomial_representative (H:B) k:
  @is_complex_weierstrass_regular_germ R X NX hNX (J H) k v ->I (J H) ->
  forall x:C,exists P:B,(forall i,(k<=i)%N ->coefficient P i = 0) /\pi (J P) = x.
Proof.
move=>hRegular hIH x.
have [alpha hAlpha]:=commutative_quotient_surjective hQuotient x.
have [a [P [hSupport hDivision]]]:=@holomorphic_polynomial_division_exists R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXi hXiValues B embed variable coefficient hP J hJ H k hRegular alpha.
have hKernel:pi (J H) = 0:=(commutative_quotient_kernel hQuotient (J H)).2 hIH.
exists P;split;first exact:hSupport.
by rewrite -hAlpha hDivision rmorphD rmorphM hKernel mulr0 add0r.
Qed.
End QuotientImage.
