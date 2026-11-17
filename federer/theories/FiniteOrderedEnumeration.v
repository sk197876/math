(** Federer (1969), 3.4.8(10), p. 332:
    enumerate each finite fibre in increasing
    order of omega_(m+1). Finite sorting
    is used only to prove existence;
    independent membership and strict-order laws
    characterize the resulting enumeration uniquely. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OrderedEnumeration.
Variable R:realType.
Variable X:choiceType.
Variable F:set X.
Variable xi:X->R.

(** Source for [is_finite_ordered_enumeration]:
    the fibre membership and strict order
    specifying psi_1,...,psi_nu in
    3.4.8(10), p. 332. These laws
    are independent of the finite sorting
    used below to prove existence. *)
Definition is_finite_ordered_enumeration (s:seq X):Prop:=
  (forall x,x \in s <->F x) /\sorted (fun x y=>xi x<xi y) s.

(** Source for [finite_ordered_enumeration_exists]:
    the actual finite fibre admits the
    increasing enumeration of 3.4.8(10),
    p. 332. Only injectivity of the
    ordering coordinate on that fibre is
    required; an empty fibre has an empty enumeration. *)
Theorem finite_ordered_enumeration_exists:
  finite_set F ->(forall x y,F x ->F y ->xi x=xi y ->x=y) ->
  exists s:seq X,is_finite_ordered_enumeration s.
Proof.
move=>hFinite hInjective.
pose raw:=fset_set F.
pose leX:=fun x y:X=>xi x<=xi y.
pose s:=sort leX (raw:seq X).
have hMember x:x \in s <->F x.
  by rewrite /s mem_sort /raw in_fset_set // inE.
have hUniq:uniq s by rewrite /s sort_uniq fset_uniq.
have hOn:{in s &,injective xi}.
  move=>x y hx hy hEqual;exact:hInjective x y ((hMember x).1 hx) ((hMember y).1 hy) hEqual.
have hMappedUniq:uniq (map xi s) by rewrite (map_inj_in_uniq hOn).
have hLe:sorted leX s:=sort_sorted (fun x y=>le_total (xi x) (xi y)) (raw:seq X).
have hLt:sorted (fun x y=>xi x<xi y) s.
  change (is_true (sorted (relpre xi <%O) s)).
  rewrite -sorted_map lt_sorted_uniq_le hMappedUniq /= sorted_map.
  exact:hLe.
by exists s;split.
Qed.

(** Source for [finite_ordered_enumeration_unique]:
    the strict fibre order characterizes the
    functions psi_lambda in 3.4.8(10),
    p. 332. Apply finite ordered-sequence
    uniqueness to their exact common membership
    set; no global coordinate injectivity is assumed. *)
Theorem finite_ordered_enumeration_unique (s t:seq X):
  is_finite_ordered_enumeration s ->is_finite_ordered_enumeration t ->s=t.
Proof.
move=>[hS hSSorted] [hT hTSorted].
have hTrans:transitive (fun x y:X=>xi x<xi y) by move=>x y z;exact:lt_trans.
have hIrr:irreflexive (fun x y:X=>xi x<xi y) by move=>x;exact:ltxx.
apply:(@irr_sorted_eq X (fun x y=>xi x<xi y) hTrans hIrr s t hSSorted hTSorted).
move=>x;apply/idP/idP=>hx.
- exact:(hT x).2 ((hS x).1 hx).
- exact:(hS x).2 ((hT x).1 hx).
Qed.
End OrderedEnumeration.
