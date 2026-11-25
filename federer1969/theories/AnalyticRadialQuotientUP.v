(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the radial Taylor quotient in a fixed vector
    direction. Its actual derivative laws precede
    existence. This auxiliary quotient supports the
    expanded finite-jet and ideal-power argument; it
    is not an additional numbered-theorem hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP SymmetricForms PolynomialTaylorTerms
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermRing AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_analytic_radial_quotient]: the mth
    derivative is the contraction of the original
    (m+1)st derivative with v, divided by m+1.
    This expands Taylor's formula of 3.1.24,
    pp. 238–239, for the ideal-closedness proof of
    3.4.8(5), p. 328. Every actual coefficient
    form gives the same equation; no choice is exposed. *)
Definition is_analytic_radial_quotient (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a
  (alpha:@analytic_germ_ring R X NX hNX a) (v:X)
  (q:@analytic_germ_ring R X NX hNX a):Prop:=
  forall m (F:S_m X R^o m.+1),
    (forall t,F t = @ContinuousMultilinear.evaluation R m.+1 X R^o NX (fun z=>`|z|)
      hNX (@scalar_absolute_value_norm R) [ffun i=>tnth t i]
      (@AnalyticGermJets.value R X NX hNX a m.+1 alpha)) ->
    forall u,@ContinuousMultilinear.evaluation R m X R^o NX (fun z=>`|z|)
      hNX (@scalar_absolute_value_norm R) u (@AnalyticGermJets.value R X NX hNX a m q) =
      ((m.+1)%:R:R)^-1*:(symmetric_taylor_term m F v [tuple u i | i<m]).
