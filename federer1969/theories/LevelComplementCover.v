(** Federer (1969), 2.3.2(7), p. 75: the complementary level set is covered
    by a separated upper level, the thin intervening strip, and the null
    omitted domain. this lemma retains the partial-domain bookkeeping. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology MeasureUP MeasureSplit
  MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [level_complement_cover_bound]: supporting final
    covering estimate in Federer 2.3.2(7), p. 75.
    The omitted domain contributes zero by the standing conull-
    domain premise; no measurability of the level sets is presumed. *)
Lemma level_complement_cover_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (T : set X) (r b : R) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  mu (T `\` partial_function_preimage f [set y | y <= r%:E]) <=
    mu (T `&` partial_function_preimage f [set y | b%:E <= y]) +
    mu (T `&` partial_function_preimage f [set y | r%:E < y /\ y <= b%:E]).
Proof.
move=> hd.
pose A := partial_function_preimage f [set y | y <= r%:E].
pose H := T `&` partial_function_preimage f [set y | b%:E <= y].
pose S := T `&` partial_function_preimage f [set y | r%:E < y /\ y <= b%:E].
pose N := T `\` partial_function_domain f.
have hn : mu N = 0.
  apply: (@measure_null_subset R X mu hm N (~` partial_function_domain f))=> //.
  by move=> x [_ hx].
have hc : T `\` A `<=` (H `|` S) `|` N.
  move=> x [hx hnA]; case: (pselect (partial_function_domain f x))=> [[y hy]|hnD].
  - left; case: (boolP (b%:E <= y))=> hby.
    + left; split=> //; by exists y.
    + right; split=> //; exists y; split=> //; split.
      * rewrite ltNge; apply/negP=> hyr; apply: hnA; by exists y.
      * have hlt : y < b%:E by rewrite ltNge; exact hby.
        exact: ltW hlt.
  - by right; split.
have hc1 := @measure_binary_cover R X mu hm (T `\` A) (H `|` S) N hc.
rewrite hn adde0 in hc1; apply: le_trans hc1 _.
exact: (@measure_binary_cover R X mu hm (H `|` S) H S (fun x hx => hx)).
Qed.
