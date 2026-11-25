(** Federer (1969), 1.8.1, p. 38: supporting compact parameter set for
    bounded finite convex combinations. Only finite products of compact real
    intervals and closed subspaces of compact spaces are used here. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets set_interval reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Simplex.
Variable R : realType.
Variable n : nat.

(** Source for [coefficient_simplex]: Federer 1.8.1, p. 38,
    supporting closed coefficient simplex: nonnegative weights of total
    at most one, allowing unused weight at zero. *)
Definition coefficient_simplex : set ('I_n -> R^o) :=
  fun a => (forall i, 0 <= a i) /\ \sum_i a i <= 1.

(** Source for [coefficient_sum_continuous]: Federer 1.8.1,
    p. 38, supporting continuity of the total weight in the compactness
    proof, from continuity of projections and finite sums. *)
Lemma coefficient_sum_continuous : continuous (fun a : 'I_n -> R^o => \sum_i a i).
Proof.
apply: continuous_big; first exact: add_continuous.
move=> i _; exact: proj_continuous.
Qed.

(** Source for [coefficient_simplex_closed]: Federer 1.8.1,
    p. 38, supporting closedness of the coefficient constraints. *)
Lemma coefficient_simplex_closed : closed coefficient_simplex.
Proof.
have heq : coefficient_simplex =
    (\bigcap_i (fun a : 'I_n -> R^o => a i) @^-1` [set r | 0 <= r]) `&`
    ((fun a : 'I_n -> R^o => \sum_i a i) @^-1` [set r | r <= 1]).
  apply/seteqP; split=> a [ha hs]; split=> //.
  - by move=> i _; exact: ha.
  - by move=> i; exact: ha i I.
rewrite heq; apply: closedI.
- apply: closed_bigI => i _; apply: preimage_closed; last exact: closed_ge.
  move=> a _; exact: proj_continuous.
- apply: preimage_closed; last exact: closed_le.
  move=> a _; exact: coefficient_sum_continuous.
Qed.

(** Source for [coefficient_simplex_coordinate_bound]: Federer
    1.8.1, p. 38, supporting boundedness: every nonnegative
    coefficient is at most the total weight, hence at most one. *)
Lemma coefficient_simplex_coordinate_bound a : coefficient_simplex a ->
  forall i, a i <= 1.
Proof.
move=> [ha hs] i; apply: (le_trans _ hs).
have hsplit : (\sum_j a j) = a i + \sum_(j | j != i) a j by rewrite (bigD1 i).
rewrite hsplit lerDl; apply: sumr_ge0 => j _; exact: ha.
Qed.

(** Source for [coefficient_simplex_compact]: Federer 1.8.1,
    p. 38, supporting compactness of the bounded coefficient domain,
    including n=0. It is a closed subset of the cube [0,1]^n. *)
Theorem coefficient_simplex_compact : compact coefficient_simplex.
Proof.
pose C : set ('I_n -> R^o) := fun a => forall i, `[0,1] (a i).
have hC : compact C.
  exact (@tychonoff _ (fun _ : 'I_n => (Topological.clone R^o _))
    (fun _ => `[0,1]) (fun _ => @segment_compact R 0 1)).
apply: (subclosed_compact coefficient_simplex_closed hC) => a ha i.
rewrite set_itvcc /=; apply/andP; split; first exact: (proj1 ha i).
exact: coefficient_simplex_coordinate_bound ha i.
Qed.
End Simplex.
