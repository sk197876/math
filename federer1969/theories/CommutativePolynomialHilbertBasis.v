(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: the project proves Hilbert's basis theorem
    from its independent polynomial coefficient laws. Stabilised
    bounded coefficient ideals and the finite bounded module
    supply generators; ordinary degree induction proves generation.
    Source: Bourbaki, Commutative Algebra (1972), Chapter III,
    section 2, no. 10, Corollary 1, p. 184. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealSealed
  CommutativePolynomialUP CommutativePolynomialDegreeBounds
  RingScalarRestriction RingSubmoduleUP RingIdealModules
  PolynomialTruncatedLeadingUP PolynomialTruncatedLeadingExistence
  PolynomialTruncatedLeadingStabilization PolynomialTruncatedLeadingLift
  PolynomialBoundedIdealModule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [commutative_polynomial_ring_noetherian]:
    Hilbert's basis theorem, Bourbaki (1972), Chapter III,
    section 2, no. 10, Corollary 1, p. 184,
    supporting the expanded ideal-closure argument for
    3.4.8(5), p. 328. No polynomial Noetherian
    theorem from another Rocq library is used. *)
Theorem commutative_polynomial_ring_noetherian (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient):
  is_noetherian_commutative_ring A ->is_noetherian_commutative_ring B.
Proof.
move=>hNoetherian I hI.
have [L hL]:=@truncated_polynomial_leading_family_exists A B coefficient I.
have [N hStable]:=@truncated_polynomial_leading_stabilizes A B embed variable coefficient hP I hI L hL hNoetherian.
pose V:=[the lmodType A of (ring_restricted_space embed B^o)].
pose M:set V:=fun P=>I P /\forall i,(N.+1<=i)%N ->coefficient P i = 0.
have [F hF]:=@bounded_polynomial_ideal_finitely_generated A B embed variable coefficient hP I hI N.+1 hNoetherian.
pose J:set B:=@GeneratedCommutativeIdeal.value B [set x:B|x \in F].
have hJ:=@GeneratedCommutativeIdeal.laws B [set x:B|x \in F].
have hJI:J `<=` I.
  apply:(@generated_commutative_ideal_minimal B _ _ hJ I hI)=>P hPF.
  exact:((@generated_ring_submodule_contains A V _ _ hF P hPF).1).
have hBounded:M `<=` J.
  apply:(@generated_ring_submodule_minimal A V _ _ hF J).
  - exact:(@ideal_restricted_ring_submodule A B embed J (generated_commutative_ideal_laws hJ)).
  - exact:(generated_commutative_ideal_contains hJ).
have hAll:forall d (P:B),I P ->(forall i,(d<i)%N ->coefficient P i = 0) ->J P.
  elim=>[|d ih] P hIP hHigh.
  - apply:hBounded;split;first exact:hIP.
    move=>i hi;apply:hHigh;exact:(leq_ltn_trans (leq0n N) hi).
  - case:(leqP d.+1 N)=>hSmall.
    + apply:hBounded;split;first exact:hIP.
      move=>i hi;apply:hHigh;exact:(leq_ltn_trans hSmall hi).
    + have hND:(N<=d.+1)%N:=ltnW hSmall.
      have hInLeading:L d.+1 (coefficient P d.+1).
        apply/(hL d.+1 (coefficient P d.+1));exists P;by split;last split.
      rewrite (hStable d.+1 hND) in hInLeading.
      have [Q [hIQ [hQHigh hEqual]]]:=(hL N (coefficient P d.+1)).1 hInLeading.
      have hQIn:J Q.
        apply:hBounded;split;first exact:hIQ.
        move=>i hi;exact:hQHigh i hi.
      pose T:B:=variable^+(d.+1-N)%N*Q.
      have hTI:I T:=@commutative_ideal_mul B I hI (variable^+(d.+1-N)%N) Q hIQ.
      have hTJ:J T:=@commutative_ideal_mul B J (generated_commutative_ideal_laws hJ)
        (variable^+(d.+1-N)%N) Q hQIn.
      have [hTHigh hTEqual]:=@truncated_polynomial_leading_lift A B embed variable coefficient hP Q N d.+1 hND hQHigh.
      have hCancel:coefficient P d.+1 = coefficient T d.+1 by rewrite /T hTEqual hEqual.
      have hDifference:=@polynomial_cancelled_leading_bound A B embed variable coefficient hP
        P T d.+1 hHigh hTHigh hCancel.
      have hDifferenceIdeal:I (P-T):=@commutative_ideal_difference B I hI P T hIP hTI.
      have hDifferenceIn:J (P-T):=ih (P-T) hDifferenceIdeal hDifference.
      have hSum:=@commutative_ideal_add B J (generated_commutative_ideal_laws hJ) (P-T) T hDifferenceIn hTJ.
      by rewrite subrK in hSum.
have hIJ:I `<=` J.
  move=>P hIP;have [d hd]:=@polynomial_coefficients_finite A B embed variable coefficient hP P.
  apply:(hAll d P hIP)=>i hi;exact:hd i (ltnW hi).
exists F.
have hEqual:I = J by apply/seteqP;split;[exact:hIJ|exact:hJI].
by rewrite hEqual.
Qed.
