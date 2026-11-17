(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the actual radial quotient lowers the vanishing
    order by one. The proof uses its public
    derivative laws and the original contraction formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP SymmetricForms PolynomialTaylorTerms
  PolynomialTaylorTermContinuity ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermRing AnalyticGermJetsSealed AnalyticGermCoefficientForms
  AnalyticRadialQuotientUP AnalyticRadialQuotientSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_radial_quotient_zero_jet]: a
    vanishing successor derivative gives a vanishing
    quotient derivative, expanding Taylor's formula of
    3.1.24, pp. 238–239, for the ideal-power
    argument in 3.4.8(5), p. 328. *)
Lemma analytic_radial_quotient_zero_jet (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a
  (alpha:@analytic_germ_ring R X NX hNX a) v m:
  @AnalyticGermJets.value R X NX hNX a m.+1 alpha = 0 ->
  @AnalyticGermJets.value R X NX hNX a m (@AnalyticRadialQuotient.map R X NX hNX a alpha v) = 0.
Proof.
move=>hZero.
have [phi [hPhi _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX a alpha.
have hForm:phi m.+1 = 0.
  apply:sform_ext=>u;by rewrite hPhi hZero linear0 sform_zeroE.
apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R m X R^o NX
  (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)))=>u.
rewrite (@AnalyticRadialQuotient.laws R X NX hNX a alpha v m (phi m.+1) (hPhi m.+1))
  hForm (symmetric_taylor_term_tuple_value (leqnSn m)) sform_zeroE !scaler0 linear0.
reflexivity.
Qed.

(** Source for [analytic_radial_quotient_lowers_order]:
    vanishing through the original order gives the
    required lower-order vanishing for every actual
    radial quotient, supporting 3.4.8(5), p. 328. *)
Lemma analytic_radial_quotient_lowers_order (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a
  (alpha:@analytic_germ_ring R X NX hNX a) v k:
  (forall i,(i<k.+1)%N ->@AnalyticGermJets.value R X NX hNX a i alpha = 0) ->
  forall i,(i<k)%N ->@AnalyticGermJets.value R X NX hNX a i
    (@AnalyticRadialQuotient.map R X NX hNX a alpha v) = 0.
Proof.
move=>hZero i hi;apply:analytic_radial_quotient_zero_jet.
exact:hZero i.+1 hi.
Qed.
