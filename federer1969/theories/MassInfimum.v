(** Federer (1969), 1.8.1, p. 39, first display: mass is the infimum of
    total Euclidean lengths of simple decompositions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import InnerProductUP ExteriorGrading ExteriorNorm
  AlternatingCoordinates LinearBasis AssociatedSubspace ComassUP MassUP
  MassDecompositionBound MassOptimalDecomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Infimum.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.
Local Notation E := (exterior_power V m).
Local Notation N := (@exterior_norm R h2 V B hB m).

(** Source for [simple_decomposition_lengths]: Federer 1.8.1, p. 39, the set
    inside the first displayed infimum. *)
Definition simple_decomposition_lengths (x : E) : set R := fun t =>
  exists k, exists u : 'I_k -> E,
    (forall i, simple (u i)) /\ x = \sum_i u i /\ t = \sum_i N (u i).

(** Source for [mass_simple_decomposition_infimum]: Federer 1.8.1,
    p. 39, the infimum formula. The preceding p. 38 decomposition
    theorem proves this infimum is attained, even in dimension zero. *)
Theorem mass_simple_decomposition_infimum n (e : 'I_n -> V)
    (he : is_basis e) (hm : (0 < m)%N)
    (kappa : A_m V R^o m -> R)
    (hk : forall phi, is_comass h2 hB phi (kappa phi)) x d :
  is_mass kappa x d -> d = inf (simple_decomposition_lengths x).
Proof.
move=> hd.
have [k [u [hkd [hu [hx hdv]]]]] :=
  @mass_optimal_simple_decomposition R h2 V B hB n e he m hm kappa hk x d hd.
have hmem : simple_decomposition_lengths x d by exists k, u.
have hne : simple_decomposition_lengths x !=set0 by exists d.
have hl : lbound (simple_decomposition_lengths x) d.
  move=> t [j [v [hv [hxv ->]]]].
  apply: (@simple_decomposition_mass_bound R h2 V B hB m hm kappa hk
    (Finite.clone 'I_j _) v d hv).
  by rewrite -hxv.
have hb : has_lbound (simple_decomposition_lengths x) by exists d.
apply/eqP; rewrite eq_le; apply/andP; split.
- exact: lb_le_inf hne hl.
- apply: (ge_inf hb); exact hmem.
Qed.
End Infimum.
