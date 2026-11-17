(** Federer (1969), 3.4.12, p. 339:
    the original unitary scalar-commutation locus is closed.
    Apply the existing closed-equalizer theorem to each
    actual operator equation, then intersect these closed sets. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import PointwiseCommutingLocusUP ContinuousEqualizerClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [pointwise_commuting_closed]: the actual
    commuting locus is closed when its action evaluations
    and the prescribed operators are continuous, supporting
    the Haar group in 3.4.12, p. 339. *)
Theorem pointwise_commuting_closed (G X:topologicalType) (I:Type)
    (action:G->X->X) (P:I->X->X) (S:set G):
  is_pointwise_commuting_locus action P S ->hausdorff_space X ->
  (forall x,continuous (fun g=>action g x)) ->
  (forall i,continuous (P i)) ->closed S.
Proof.
move=>hS hX hAction hP.
have hSame:S=\bigcap_(i in [set:I]) \bigcap_(x in [set:X])
    [set g:G|action g (P i x)= P i (action g x)].
  apply/seteqP;split=>g.
  - move/(hS g)=>hG i _ x _;exact:hG i x.
  - move=>hG;apply/(hS g)=>i x;exact:hG i Logic.I x Logic.I.
rewrite hSame;apply:closed_bigI=>i _;apply:closed_bigI=>x _.
apply:(@continuous_equalizer_closed G X (fun g=>action g (P i x))
  (fun g=>P i (action g x)) hX);first exact:hAction.
move=>g;exact:continuous_comp (hAction x g) (hP i (action g x)).
Qed.
