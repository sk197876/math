(** Supporting Federer (1969), 3.4.8(5), p. 328:
    every ideal in the actual finite-dimensional
    analytic germ ring is closed for the original
    derivative metric. The proof expands the printed
    measurability argument through actual finite jets,
    coordinate factorisation and ideal Krull intersection.
    No ideal closedness is supplied as a hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP LinearBasis AnalyticGermRing AnalyticGermMetric
  AnalyticGermJetsSealed AnalyticGermJetDifference CommutativeIdealUP
  AnalyticIdealClosureFiniteJets AnalyticVanishingToIdealPower AnalyticGermAdicSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_germ_ideal_closed]:
    an original ideal is closed in the actual
    derivative metric, expanding the measurability proof
    for 3.4.8(5), p. 328. Every closure
    member agrees with an ideal member to each
    finite order; proved coordinate factorisation gives
    approximation modulo each ideal power, and the
    proved intersection theorem gives original membership.
    All centres and finite dimensions remain. *)
Theorem finite_analytic_germ_ideal_closed (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b) a
  (I:set (@analytic_germ_ring R X NX hNX a)):
  is_commutative_ideal I ->@closed (@analytic_germ_metric R X NX hNX a) I.
Proof.
move=>hI alpha hClosure.
apply:(@finite_analytic_ideal_adic_separation R X NX hNX n b hb a I hI alpha)=>k.
have [beta [hBeta hAgree]]:=@analytic_ideal_closure_finite_jet_agreement R X NX hNX n b hb a
  I hI alpha hClosure k.
exists beta;split=>//.
refine (@finite_analytic_vanishing_to_ideal_power R X NX hNX n b hb a k _ _).
move=>i hi.
by rewrite analytic_germ_jet_difference (hAgree i hi) subrr.
Qed.
