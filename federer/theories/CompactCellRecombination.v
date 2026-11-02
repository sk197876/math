(** Federer (1969), 2.10.47, p. 205: take the finite union of compact
    subsets D_S chosen inside the coarse cells. The union stays compact and
    inside the preceding set, and its content in each cell equals that of
    the corresponding D_S because all other cells meet it in null
    boundaries. This lemma isolates that recombination argument; the
    intermediate values are furnished separately. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostBasic MeasureNullModification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_finite_indexed_union]: supporting
    compactness of E_j as a finite union in 2.10.47,
    p. 205. This is a general topological fact;
    no metric or nonemptiness premise is needed. *)
Lemma compact_finite_indexed_union (T : topologicalType) (J : choiceType)
    (D : set J) (F : J -> set T) : finite_set D ->
  (forall j, D j -> compact (F j)) -> compact (\bigcup_(j in D) F j).
Proof.
move=> /finite_fsetP [B ->]; elim/fset1U_rect: B=> [|a B ha IH] hF.
- rewrite set_fset0 bigcup_set0; exact: compact0.
- rewrite set_fsetU1 bigcup_setU1; rewrite set_fsetU1 in hF; apply: compactU.
  + apply: hF; by left.
  + apply: IH=> j hj; apply: hF; by right.
Qed.

(** Source for [compact_cell_recombination]: supporting
    local-value preservation under E_j=union D_S in
    2.10.47, p. 205. The chosen D_S need not
    be measurable for the content; only null overlaps
    of the surrounding coarse cells are used. *)
Theorem compact_cell_recombination (R : realType) (X : metricType R) (J : finType)
    (mu : set X -> \bar R) (hm : is_measure mu) (E : set X)
    (F : J -> set X) (a : J -> \bar R) :
  (forall j k, j != k -> mu ((E `&` F j) `&` F k)=0) ->
  (forall j, exists D, [/\ compact D, D `<=` (E `&` F j) & mu D=a j]) ->
  exists K, [/\ compact K, K `<=` E & forall j, mu (K `&` F j)=a j].
Proof.
move=> hover hex.
pose D j := projT1 (cid (hex j)).
have hD j : [/\ compact (D j), D j `<=` (E `&` F j) & mu (D j)=a j] := projT2 (cid (hex j)).
have hDc j : compact (D j) by have [hh _ _] := hD j.
have hDs j : D j `<=` (E `&` F j) by have [_ hh _] := hD j.
have hDv j : mu (D j)=a j by have [_ _ hh] := hD j.
pose K := \bigcup_j D j.
exists K; split.
- exact (@compact_finite_indexed_union X J setT D (@finite_finset J setT)
    (fun j _=>hDc j)).
- move=> x [j _ hx]; exact: (hDs j x hx).1.
- move=> j; rewrite -(hDv j).
  pose N := \bigcup_(k in [set k | k != j]) ((E `&` F j) `&` F k).
  have hN : mu N=0.
    apply: (measure_null_countable_union hm (finite_set_countable (@finite_finset J _)))=> k hk.
    apply: hover; by rewrite eq_sym.
  apply: (@measure_null_modification_value R X mu hm (K `&` F j) (D j) N hN)=> x hn.
  split.
  + move=> [[k _ hxk] hxj]; case: (eqVneq k j)=> [he|hne]; first by rewrite -he.
    exfalso; apply: hn; exists k; first exact hne.
    split; last exact: (hDs k x hxk).2.
    split; [exact: (hDs k x hxk).1 | exact hxj].
  + move=> hx; split; last exact: (hDs j x hx).2.
    by exists j.
Qed.
