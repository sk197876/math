(** Federer (1969), 2.5.5, p. 97: preserve convergence when extracting the
    second subsequence. The underlying convergence in measure is 2.3.8, p.
    78, and the extraction theorem is 2.3.10, p. 80. These elementary
    subsequence laws make that step explicit, including partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionLimitUP
  MeasureUP MeasureConvergenceUP CauchyIndexSelectionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [strict_subsequence_topological_limit]: general topology
    supporting the second extraction in Federer 2.5.5, p. 97 *)
Lemma strict_subsequence_topological_limit (Y : topologicalType) (u : nat -> Y)
    (y : Y) (s : nat -> nat) :
  (forall n, (s n < s n.+1)%N) -> u @ \oo --> y -> (fun n => u (s n)) @ \oo --> y.
Proof.
move=> hs hu U hU; have [N _ hN] := hu U hU.
exists N=> // n hn.
apply: hN; exact: leq_trans hn (@strict_index_sequence_dominates s hs n).
Qed.

(** Source for [partial_limit_locus_subsequence]: preservation of pointwise
    convergence with all original defined values, used in Federer 2.5.5, p.
    97 *)
Lemma partial_limit_locus_subsequence (X : Type) (Y : topologicalType)
    (f : nat -> partial_function X Y) (g : partial_function X Y) (s : nat -> nat) :
  (forall n, (s n < s n.+1)%N) ->
  partial_function_limit_locus f g `<=` partial_function_limit_locus (fun n => f (s n)) g.
Proof.
move=> hs x [u [y [hu [hy hl]]]].
exists (fun n => u (s n)),y; split; first by move=> n; exact: hu.
split=> //; exact: (@strict_subsequence_topological_limit Y u y s hs hl).
Qed.

(** Source for [converges_in_measure_subsequence]: preservation of
    convergence for the second measure after the first extraction, Federer
    2.5.5, p. 97 No finite-total-measure assumption is needed. *)
Lemma converges_in_measure_subsequence (R : realType) (X : choiceType)
    (V : lmodType R) (mu : set X -> \bar R) (N : V -> R)
    (f : nat -> partial_function X V) (g : partial_function X V) (s : nat -> nat) :
  (forall n, (s n < s n.+1)%N) -> converges_in_measure mu N f g ->
  converges_in_measure mu N (fun n => f (s n)) g.
Proof.
move=> hs hf e he; have [K hK] := hf e he.
exists K=> n hn; apply: hK.
exact: leq_trans hn (@strict_index_sequence_dominates s hs n).
Qed.
