(** Federer (1969), 1.8.1, p. 38, second supremum definition: mass is dual
    to comass. The comass function is a parameter obeying its independent
    laws; the mass is specified before proving existence or attainment. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP ExteriorGrading AlternatingCoordinates
  AlternatingPairing ComassUP ComassBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Specification.
Variable R : rcfType.
Variable V : lmodType R.
Variable m : nat.
Variable kappa : A_m V R^o m -> R.

(** Source for [is_mass]: Federer 1.8.1, p. 38, second
    displayed supremum: upper bounds and positive-error approximation
    on the comass unit ball specify the mass of a multivector. *)
Record is_mass (x : exterior_power V m) (d : R) : Prop := {
  mass_upper_law : forall phi, kappa phi <= 1 -> pairing x phi <= d;
  mass_approx_law : forall eps, 0 < eps ->
    exists phi, kappa phi <= 1 /\ d-eps < pairing x phi
}.

(** Source for [mass_least_upper_bound]: Federer 1.8.1,
    p. 38, supporting least-upper-bound consequence of the specification. *)
Lemma mass_least_upper_bound x d (hd : is_mass x d) b :
  (forall phi, kappa phi <= 1 -> pairing x phi <= b) -> d <= b.
Proof.
move=> hb; case: (leP d b) => // hbd.
have he : 0 < d-b by rewrite subr_gt0.
have [phi [hphi hh]] := mass_approx_law hd he.
rewrite opprB addrCA subrr addr0 in hh.
have h := lt_le_trans hh (hb phi hphi).
by rewrite ltxx in h.
Qed.

(** Source for [mass_unique]: Federer 1.8.1, p. 38,
    supporting uniqueness of the number defined by the second supremum. *)
Theorem mass_unique x d e : is_mass x d -> is_mass x e -> d=e.
Proof.
move=> hd he; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@mass_least_upper_bound x d hd e (@mass_upper_law x e he)).
- exact (@mass_least_upper_bound x e he d (@mass_upper_law x d hd)).
Qed.
End Specification.
