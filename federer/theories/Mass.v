(** Federer (1969), 1.8.1, p. 38: public mass interface, using the
    independently specified comass. No private supremum construction is
    exposed to downstream proofs. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import InnerProductUP ExteriorGrading AlternatingCoordinates
  AlternatingPairing LinearBasis ComassUP Comass
  MassUP MassBounds MassSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Interface.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Hypothesis hm : (0 < m)%N.
Local Notation kappa := (@comass R h2 V B hB n e he m hm).
Local Notation hk := (@comassP R h2 V B hB n e he m hm).

(** Source for [mass]: Federer 1.8.1, p. 38, mass
    supplied by its sealed dual supremum specification. *)
Definition mass (x : exterior_power V m) :=
  @Mass.norm R h2 V B hB n e he m hm kappa hk x.

(** Source for [massP]: Federer 1.8.1, p. 38, the
    public mass satisfies its defining dual supremum laws. *)
Theorem massP x : is_mass kappa x (mass x).
Proof. exact: Mass.laws. Qed.

(** Source for [mass_supremum]: Federer 1.8.1, p. 38,
    the second defining display: mass is the supremum of evaluations
    against covectors with comass at most one. *)
Theorem mass_supremum x : mass x =
  sup ((fun phi => pairing x phi) @` [set phi | kappa phi <= 1]).
Proof.
pose D := (fun phi => pairing x phi) @` [set phi | kappa phi <= 1].
have hn : D !=set0.
  exists (pairing x 0); exists 0 => //.
  change (kappa (0 : A_m V R^o m) <= 1).
  by rewrite (@comass_function_zero R h2 V B hB m hm kappa hk).
have hb : ubound D (mass x).
  move=> r [phi hphi <-].
  exact (@mass_upper_law R V m kappa x (mass x) (massP x) phi hphi).
have hu : has_sup D by split=> //; exists (mass x).
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@mass_least_upper_bound R V m kappa x (mass x) (massP x) (sup D)) => phi hphi.
  apply: (sup_upper_bound hu); by exists phi.
- exact: ge_sup hn hb.
Qed.
End Interface.
