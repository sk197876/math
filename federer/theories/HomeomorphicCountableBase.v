(** General topology supporting Federer (1969), 3.2.46,
    pp. 281–282: the countable chart base transfers through
    the proved topology identity. Only open-preimage laws and
    the independent countable-base specification are used. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [homeomorphic_countable_base]: the same
    countable base is available for local measure arguments
    after the topology identification in 3.2.46, p. 281.
    This is supporting general topology, including empty spaces. *)
Lemma homeomorphic_countable_base (X Y : topologicalType)
    (f : X -> Y) (g : Y -> X) (U : nat -> set X) :
  cancel f g -> cancel g f -> continuous f -> continuous g ->
  is_countable_open_base U ->
  is_countable_open_base (fun i=>g @^-1` U i).
Proof.
move=> hFG hGF hF hG hBase; constructor.
- move=> i; apply: open_comp; first by move=> x _; exact: hG.
  exact: countable_base_open hBase i.
- by rewrite (countable_base_empty hBase) preimage_set0.
- move=> V hV y hy.
  have hPre : open (f @^-1` V).
    apply: open_comp; first by move=> x _; exact: hF.
    exact hV.
  have hPoint : (f @^-1` V) (g y) by change (V (f (g y))); rewrite hGF.
  have [i [hi hSub]] := countable_base_refines hBase hPre hPoint.
  exists i; split; first exact hi.
  move=> z hz; have h := hSub (g z) hz.
  change (V (f (g z))) in h; by rewrite hGF in h.
Qed.
