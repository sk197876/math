(** Federer (1969), 2.5.20, p. 114: supporting countable tests for the
    support assertion. Every subset of E=K(Y) admits countably many uniform
    approximation tests. In particular this applies to functions supported
    inside any chosen basic open set. The proof chooses representatives from
    the finite rational cells already used for separability; no completeness
    is assumed. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology lra.
From Federer Require Import CompactFunctionSpaceUP CompactFunctionSpaceLaws
  CompactFunctionCountableCells CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_function_subset_countable_approximation]:
    supporting countable dense tests for the support inclusion
    of Federer 2.5.20, p. 114. The subset need not be
    closed, nonempty, or a vector subspace. *)
Theorem compact_function_subset_countable_approximation (R : realType) (Y : topologicalType)
    (E : lmodType R) (ev : E -> Y -> R) (hE : is_compact_function_space ev)
    (B : nat -> set Y) (S : set E) :
  compact (@setT Y) -> is_countable_open_base B ->
  exists D : set E, countable D /\ D `<=` S /\
    forall v, S v -> forall e : R, 0<e ->
      exists u, D u /\ compact_function_norm ev (v-u)<e.
Proof.
move=> hY hB.
pose J := [the countType of (seq (nat*rat*rat) : Type)].
pose C := @compact_function_interval_cell R Y E ev B.
pose A : set J := [set s | exists v, S v /\ C s v].
have hchoose (s : J) : exists v : E, A s -> S v /\ C s v.
  case: (pselect (A s))=> [[v hv]|hn].
  - by exists v.
  - exists 0=> hs; exact: False_ind _ (hn hs).
pose pick s := projT1 (cid (hchoose s)).
have hpick s := projT2 (cid (hchoose s)).
exists (pick @` A); split.
- apply: sub_countable (card_image_le _ _) _; exact: countableP.
- split.
  + move=> u [s hs <-]; exact: (hpick s hs).1.
  + move=> v hv e he.
    have hd : 0<e/2 by rewrite divr_gt0 // ltr0n.
    have [s [hc [hw hs]]] := @compact_function_interval_cell_cover R Y E ev B hE hB v (e/2) hY hd.
    have hAs : A s by exists v.
    have hp := (hpick s hAs).2.
    exists (pick s); split; first by exists s.
    have hb := @compact_function_same_cell_norm_bound R Y E ev B hE s v (pick s)
      (e/2) (ltW hd) hc (fun j hj => ltW (hw j hj)) hs hp.
    have hhalf : e/2<e by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
    exact: le_lt_trans hb hhalf.
Qed.
