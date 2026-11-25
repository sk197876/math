(** Federer (1969), 2.2.10, p. 66: replacing the real coordinate of a closed
    projection by a closed subset of N. The supporting lemma allows any
    target of such a bijection. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace SuslinSetUP ClosedSequenceBijectionUP TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [closed_projection_transfer]: supporting pullback argument
    for C={(x,n): n in B, (x,psi(n)) in A} in Federer 2.2.10, p. 66.
    Closedness, image and univalence transfer from A along the closed-domain
    continuous bijection psi. *)
Lemma closed_projection_transfer (R : realType) (X Y : topologicalType)
    (S : set X) (A : set (X * Y))
    (B : set (positive_sequence_space R)) (psi : positive_sequence_space R -> Y) :
  is_closed_sequence_bijection B psi -> closed A -> fst @` A = S ->
  (forall p q, A p -> A q -> p.1 = q.1 -> p = q) ->
  has_univalent_closed_projection R S.
Proof.
move=> hpsi hA hAS hinj.
pose F (p : X * positive_sequence_space R) := (p.1,psi p.2).
have hF : continuous F.
  apply: topological_pair_continuous.
  - exact: first_projection_continuous.
  - move=> p; exact: continuous_comp
      (@second_projection_continuous X (positive_sequence_space R) p)
      (@closed_sequence_bijection_continuous R Y B psi hpsi p.2).
pose C := [set p : X * positive_sequence_space R | B p.2 /\ A (F p)].
exists C; constructor.
- apply: closedI.
  + apply: (proj1 (continuous_closedP (@snd X (positive_sequence_space R))) _ B).
    * exact: second_projection_continuous.
    * exact: closed_sequence_bijection_domain_closed hpsi.
  + exact: (proj1 (continuous_closedP F) hF A hA).
- rewrite -hAS; apply/seteqP; split.
  + move=> x [[y n] [hn ha] <-]; by exists (y,psi n).
  + move=> x [[y t] ha <-].
    have ht : (psi @` B) t by rewrite (closed_sequence_bijection_surjective hpsi).
    have [n hn he] := ht; exists (y,n)=> //; split=> //.
    change (A (y,psi n)); by rewrite he.
- move=> [x n] [y m] [hn ha] [hm hb] he.
  have hp := hinj (x,psi n) (y,psi m) ha hb he.
  have hnm : n = m.
    apply: (@closed_sequence_bijection_injective R Y B psi hpsi n m hn hm).
    exact: (congr1 (@snd X Y) hp).
  change (x = y) in he; by rewrite he hnm.
Qed.
