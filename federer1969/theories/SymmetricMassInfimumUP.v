(** Federer (1969), 1.10.5, p. 48, the infimum formula for the mass of a
    symmetric vector. This is the infimum characterization, stated
    separately from the dual supremum definition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import SymmetricAlgebra SymmetricGrading SymmetricDecompositions
  SymmetricDecompositionCosts.
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
Variable m : nat.

(** Source for [symmetric_decomposition_costs]: Federer 1.10.5,
    p. 48, the set of all candidate finite costs for a fixed vector. *)
Definition symmetric_decomposition_costs (x : symmetric_power V m) : set R :=
  fun r => exists s, symmetric_decomposition x s /\ r = symmetric_decomposition_cost N s.

(** Source for [is_symmetric_mass_infimum]: Federer 1.10.5,
    p. 48, abstract characterization of the infimum: a nonnegative
    lower bound of all decomposition costs with arbitrarily close costs
    above it. This does not assume that a minimizing decomposition exists. *)
Record is_symmetric_mass_infimum (x : symmetric_power V m) (c : R) : Prop := {
  symmetric_mass_infimum_nonnegative : 0 <= c;
  symmetric_mass_infimum_lower : forall s, symmetric_decomposition x s ->
    c <= symmetric_decomposition_cost N s;
  symmetric_mass_infimum_approximate : forall eps, 0 < eps -> exists s,
    symmetric_decomposition x s /\ symmetric_decomposition_cost N s < c+eps
}.

(** Source for [symmetric_mass_infimum_greatest]: Federer 1.10.5,
    p. 48, supporting greatest-lower-bound consequence of the
    approximation specification. Every lower bound is below the mass infimum. *)
Lemma symmetric_mass_infimum_greatest x c (hc : is_symmetric_mass_infimum x c) b :
  (forall s, symmetric_decomposition x s -> b <= symmetric_decomposition_cost N s) -> b <= c.
Proof.
move=> hb; case: (leP b c)=> // hcb.
have he : 0 < b-c by rewrite subr_gt0.
have [s [hs hh]] := @symmetric_mass_infimum_approximate x c hc (b-c) he.
rewrite addrC subrK in hh.
have h := le_lt_trans (hb s hs) hh; by rewrite ltxx in h.
Qed.

(** Source for [symmetric_mass_infimum_unique]: Federer 1.10.5,
    p. 48, supporting uniqueness of the specified real infimum. *)
Theorem symmetric_mass_infimum_unique x c d :
  is_symmetric_mass_infimum x c -> is_symmetric_mass_infimum x d -> c=d.
Proof.
move=> hc hd; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@symmetric_mass_infimum_greatest x d hd c (@symmetric_mass_infimum_lower x c hc)).
- exact (@symmetric_mass_infimum_greatest x c hc d (@symmetric_mass_infimum_lower x d hd)).
Qed.
End Specification.
