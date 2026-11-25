(** Federer (1969), 3.4.5, p. 321: finite actual
    analytic comparisons determine the original analytic remainder.
    The actual identity theorem is 3.1.24, p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import RealNormUP HilbertFormCompactness ContinuousMultilinearUP ContinuousMultilinearSealed
  NormAnalyticUP NormFiniteJetAgreement NormAnalyticFlatIdentity
  ScalarLowerHalfLineConnected ScalarAnalyticRightZeroJets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Comparisons.
Variable R:realType.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i R^o R^o N N hN hN).
Local Notation J:=([set z:R^o|z<1]).
Local Notation AN f:=(@norm_analytic R R^o R^o N N hN hN J f).

(** Source for [scalar_analytic_finite_flat_comparison]: if
    every original finite jet agrees with an actual analytic
    function zero on the original positive interval, the
    original function is zero throughout the lower half-axis,
    supporting 3.4.5, p. 321. The finite witnesses
    may vary with the derivative order. *)
Theorem scalar_analytic_finite_flat_comparison (f:R->R):
  AN f ->
  (forall m,exists g:R->R,AN g /\
    norm_finite_jet_agreement N ev NZ J J f g m 0 /\
    forall t,0<t<1 ->g t=0) ->
  forall z,J z ->f z=0.
Proof.
move=>hf hComparisons.
apply:(@norm_analytic_flat_identity R R^o R^o N N hN hN J f 0
  (@scalar_lower_half_line_connected R 1) hf (ltr01))=>m z hz.
have [g [hg [hAgree hZero]]]:=hComparisons m.
have hg0:=hg 0 (ltr01).
exact:(@scalar_analytic_right_zero_jets R J g 1 hg0 (ltr01) hZero m z
  ((hAgree m (leqnn m) z).1 hz)).
Qed.
End Comparisons.
