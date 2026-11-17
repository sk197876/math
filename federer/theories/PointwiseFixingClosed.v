(** Federer (1969), 3.4.8(4), p. 326:
    the original fixed-vector subgroups are closed.
    Each equation is a continuous preimage of a singleton. *)
From mathcomp Require Import all_boot all_order boolp classical_sets topology.
From Federer Require Import PointwiseFixingLocusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [pointwise_fixing_closed]: the original
    pointwise fixing subgroup is closed in O(n),
    supporting its Haar measure in 3.4.8(4), p. 326. *)
Theorem pointwise_fixing_closed (G X:topologicalType) (action:G->X->X) n
  (e:'I_n->X) (J:set 'I_n) (S:set G):
  is_pointwise_fixing_locus action e J S ->hausdorff_space X ->
  (forall x,continuous (fun g=>action g x)) ->closed S.
Proof.
move=>hS hX hContinuous.
have hSame:S = \bigcap_(i in J) [set g:G|action g (e i) = e i].
  apply/seteqP;split=>g.
  - move/(hS g)=>hG i hi;exact:hG.
  - move=>hG;apply/(hS g)=>i hi;exact:hG.
rewrite hSame;apply:closed_bigI=>i hi.
have hPoint:closed [set e i] by exact:accessible_closed_set1 (hausdorff_accessible hX) (e i).
apply:preimage_closed hPoint=>g _;exact:hContinuous.
Qed.
