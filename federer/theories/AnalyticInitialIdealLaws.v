(** Federer (1969), 3.4.11, p. 338:
    the original leading ideal is an actual proper
    ideal and contains every original initial polynomial
    germ. Its least-ideal laws and actual zero centre
    values prove these facts. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRing CommutativeIdealUP
  AnalyticInitialPolynomialGermUP AnalyticInitialPolynomialLaws AnalyticInitialIdealSealed
  AnalyticVanishingIdealSealed AnalyticVanishingIdealLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Laws.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variable I:set G.
Local Notation K:=(@AnalyticInitialIdeal.value R X NX hNX I).

(** Source for [analytic_initial_ideal_is_ideal]: the
    original leading polynomial ideal in 3.4.11,
    p. 338, satisfies every actual ideal law. *)
Lemma analytic_initial_ideal_is_ideal:is_commutative_ideal K.
Proof. exact:generated_commutative_ideal_laws (@AnalyticInitialIdeal.laws R X NX hNX I). Qed.

(** Source for [analytic_initial_ideal_contains]: every
    original initial polynomial germ belongs to the
    original leading ideal, 3.4.11, p. 338. *)
Lemma analytic_initial_ideal_contains alpha beta:
  I alpha ->is_initial_polynomial_germ alpha beta ->K beta.
Proof.
move=>hI hInitial.
apply:(generated_commutative_ideal_contains (@AnalyticInitialIdeal.laws R X NX hNX I)).
by exists alpha.
Qed.

(** Source for [analytic_initial_ideal_vanishes]: every
    germ in the leading ideal vanishes at the
    original centre, as used in 3.4.11, p. 338. *)
Lemma analytic_initial_ideal_vanishes:
  K `<=` @AnalyticVanishingIdeal.value R X NX hNX 0.
Proof.
apply:(generated_commutative_ideal_minimal (@AnalyticInitialIdeal.laws R X NX hNX I)
  (@analytic_vanishing_ideal_is_ideal R X NX hNX 0)).
move=>beta [alpha [_ hInitial]].
apply/(@AnalyticVanishingIdeal.laws R X NX hNX 0 beta).
exact:(analytic_initial_polynomial_germ_zero_value hInitial).
Qed.

(** Source for [analytic_initial_ideal_proper]: the
    original leading ideal is proper because one
    does not vanish at zero, 3.4.11, p. 338. *)
Lemma analytic_initial_ideal_proper:~K 1.
Proof.
move=>hOne;exact:(@analytic_vanishing_ideal_proper R X NX hNX 0
  (analytic_initial_ideal_vanishes hOne)).
Qed.
End Laws.
