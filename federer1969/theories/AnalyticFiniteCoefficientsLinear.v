(** Supporting Federer (1969), 3.4.8(5), p. 328:
    actual finite Taylor coefficients are linear over the
    original scalar constants. Derive this from their independent
    value law and the already proved original jet arithmetic. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP RingScalarRestriction AnalyticGermRing AnalyticGermSealed
  AnalyticGermJetsSealed AnalyticGermJetArithmetic AnalyticScalarsSealed
  WeierstrassScalarGermArithmetic FiniteJetDegreeIndices AnalyticFiniteCoefficientsUP
  AnalyticFiniteCoefficientsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Linearity.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable n:nat.
Variable e:'I_n->X.
Variable l:nat.
Variable a:X.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Local Notation scalar:=(@AnalyticScalars.map R X NX hNX a).
Local Notation V:=[the lmodType R of ring_restricted_space scalar G^o].
Local Notation W:=[the lmodType R of {ffun finite_jet_degree_indices n l->R^o}].

(** Source for [analytic_finite_coefficient_linear]: supporting
    actual coefficient arithmetic for Federer 3.4.8(5), p. 328.
    The original constant germs give the scalar action; every
    derivative and factorial remains as independently specified. *)
Theorem analytic_finite_coefficient_linear (f:G->W):
  is_analytic_finite_coefficient_map e f ->linear (f:V->W).
Proof.
move=>hF c alpha beta;apply/ffunP=>j.
rewrite !ffunE /=.
change (f (scalar c*alpha+beta) j = c*f alpha j+f beta j).
rewrite !hF analytic_germ_jet_add
  (@AnalyticScalars.laws R X NX hNX a c) weierstrass_scalar_germ_jet
  linearD linearZ /=.
by rewrite mulrDr mulrCA.
Qed.

(** Source for [analytic_finite_coefficient_hom]: hierarchy adapter
    exposing the proved original scalar linearity of the opaque
    coefficient map, supporting Federer 3.4.8(5), p. 328. *)
Definition analytic_finite_coefficient_hom:{linear V->W}:=
  HB.pack (@AnalyticFiniteCoefficients.map R X NX hNX n e l a)
    (GRing.isLinear.Build R V W *:%R (@AnalyticFiniteCoefficients.map R X NX hNX n e l a)
      (analytic_finite_coefficient_linear (@AnalyticFiniteCoefficients.laws R X NX hNX n e l a))).
End Linearity.
