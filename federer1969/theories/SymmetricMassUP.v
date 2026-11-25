(** Federer (1969), 1.10.5, p. 48, the supremum defining the mass of a
    symmetric vector. The mass is specified by upper bounds and
    positive-error approximation; attainment and equality with the
    decomposition infimum are proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal.
From Federer Require Import RealNormUP SymmetricAlgebra SymmetricGrading
  SymmetricForms SymmetricPairing SymmetricOperatorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Specification.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Variable hN : is_real_seminorm N.
Variable m : nat.
Local Notation kappa := (symmetric_operator_norm (W:=R^o) hN (fun r:R=>`|r|)).

(** Source for [symmetric_mass_unit_values]: Federer 1.10.5,
    p. 48, the set of scalar pairings with symmetric forms of
    operator norm at most one. The operator norm itself may be infinite. *)
Definition symmetric_mass_unit_values (x : symmetric_power V m) : set R :=
  fun r => exists phi : S_m V R^o m, (kappa phi <= 1)%E /\ r = symmetric_pairing x phi.

(** Source for [is_symmetric_mass]: Federer 1.10.5,
    p. 48, abstract least-upper-bound specification of the mass.
    Positive-error approximation does not presuppose an attaining covector. *)
Record is_symmetric_mass (x : symmetric_power V m) (c : R) : Prop := {
  symmetric_mass_upper_law : forall phi : S_m V R^o m,
    (kappa phi <= 1)%E -> symmetric_pairing x phi <= c;
  symmetric_mass_approx_law : forall eps, 0 < eps -> exists phi : S_m V R^o m,
    (kappa phi <= 1)%E /\ c-eps < symmetric_pairing x phi
}.

(** Source for [symmetric_mass_least]: Federer 1.10.5,
    p. 48, supporting least-upper-bound consequence of the specification. *)
Lemma symmetric_mass_least x c (hc : is_symmetric_mass x c) b :
  (forall phi : S_m V R^o m, (kappa phi <= 1)%E -> symmetric_pairing x phi <= b) -> c<=b.
Proof.
move=> hb; case: (leP c b)=> // hbc.
have he : 0 < c-b by rewrite subr_gt0.
have [phi [hp hh]] := @symmetric_mass_approx_law x c hc (c-b) he.
rewrite opprB addrCA subrr addr0 in hh.
have h := lt_le_trans hh (hb phi hp); by rewrite ltxx in h.
Qed.

(** Source for [symmetric_mass_unique]: Federer 1.10.5,
    p. 48, supporting uniqueness of the mass specified by the supremum. *)
Theorem symmetric_mass_unique x c d :
  is_symmetric_mass x c -> is_symmetric_mass x d -> c=d.
Proof.
move=> hc hd; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@symmetric_mass_least x c hc d (@symmetric_mass_upper_law x d hd)).
- exact (@symmetric_mass_least x d hd c (@symmetric_mass_upper_law x c hc)).
Qed.
End Specification.
