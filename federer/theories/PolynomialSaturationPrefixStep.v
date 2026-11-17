(** Federer (1969), 3.4.8(10), p. 331:
    the original bounded polynomial step
    reduces the delta-saturation argument to
    the preceding coordinate ring. Apply
    the checked scaled-polynomial representative and
    the independent saturation ideal laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeQuotientUP CommutativeSubringUP
  CommutativeIdealSaturationUP CommutativeIdealSaturationLaws CommutativePolynomialUP
  CommutativePolynomialEvaluationUP PolynomialScaledEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [polynomial_saturation_prefix_step]:
    the original bounded polynomial belongs
    to the equation ideal after multiplication
    by some delta power, once the
    preceding-prefix assertion is known,
    3.4.8(10), p. 331. The auxiliary
    quotient only records the already proved
    saturation; its construction is not used. *)
Theorem polynomial_saturation_prefix_step (A B C D:comNzRingType)
  (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (phi:{rmorphism A->C}) (t:C) (J:{rmorphism B->C})
  (F I S Q:set C) (delta z:C) (pi:{rmorphism C->D}) (W:B) N:
  is_commutative_ideal F ->is_commutative_ideal I ->
  is_commutative_ideal_saturation F delta S ->is_commutative_ideal_quotient S pi ->
  S `<=` I ->is_commutative_subring Q ->(forall a:A,Q (phi a)) ->Q delta ->Q z ->
  (forall x:C,I x ->Q x ->S x) ->S (delta*t-z) ->
  is_commutative_polynomial_evaluation embed variable phi t J ->
  (forall i,(N<=i)%N ->coefficient W i = 0) ->I (J W) ->S (J W).
Proof.
move=>hF hI hS hPi hSI hQ hCoefficients hDelta hZ hPrevious hRelation hJ hSupport hMember.
have hSIdeal:=@commutative_ideal_saturation_is_ideal C F delta S hF hS.
have hZero:pi (delta*t-z) = 0:=(commutative_quotient_kernel hPi _).2 hRelation.
have hFieldRelation:pi delta*pi t = pi z.
  apply/eqP;by rewrite -subr_eq0 -rmorphM -rmorphB hZero eqxx.
have [q [hInQ hEquivalent]]:=@polynomial_scaled_subring_representative A B C D embed variable coefficient
  hP phi t J pi Q delta z W N hJ hQ hCoefficients hDelta hZ hFieldRelation hSupport.
have hDifference:S (delta^+N*J W-q).
  apply:(commutative_quotient_kernel hPi _).1;by rewrite rmorphB hEquivalent subrr.
have hOriginalProduct:I (delta^+N*J W):=@commutative_ideal_mul C I hI (delta^+N) (J W) hMember.
have hOriginalQ:I q.
  have hDifferenceI:=hSI _ hDifference.
  have h:=@commutative_ideal_add C I hI (delta^+N*J W) (-(delta^+N*J W-q))
    hOriginalProduct (@commutative_ideal_opp C I hI _ hDifferenceI).
  by rewrite opprB addrCA subrr addr0 in h.
have hQMember:S q:=hPrevious q hOriginalQ hInQ.
have hProduct:=@commutative_ideal_add C S hSIdeal (delta^+N*J W-q) q hDifference hQMember.
rewrite subrK in hProduct.
exact:(@commutative_ideal_saturation_cancel_power C F delta S hF hS N (J W)).1 hProduct.
Qed.
