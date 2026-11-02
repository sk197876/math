(** Federer (1969), 3.2.31, p. 269: supporting passage
    from countably many compact or class-one source pieces to
    the original source. Countably many target-null exceptions
    combine into a single exception. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureIndexedCover NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [almost_null_fibres_countable_cover]: supporting
    countable source reduction in Federer 3.2.31, p. 269.
    If each covering piece has null fibres almost everywhere,
    so does every subset of their union. Source measurability,
    finite mass, disjointness and measurable fibres are unnecessary. *)
Theorem almost_null_fibres_countable_cover (R:realType) (X Y:choiceType)
    (nu:set X->\bar R) (beta:set Y->\bar R) (hn:is_measure nu) (hb:is_measure beta)
    (F:X->Y) (A:set X) (C:nat->set X):
  A `<=` \bigcup_i C i ->
  (forall i,measure_almost_everywhere beta [set y|nu (C i `&` F @^-1` [set y])=0]) ->
  measure_almost_everywhere beta [set y|nu (A `&` F @^-1` [set y])=0].
Proof.
move=>hCover hNull.
have hAll:=@measure_almost_everywhere_countable R Y [the choiceType of (nat:Type)]
  beta hb setT (fun i=>[set y|nu (C i `&` F @^-1` [set y])=0])
  (countableP _) (fun i _=>hNull i).
apply:(@measure_almost_everywhere_mono R Y beta hb _ _ _ hAll)=>y hy.
have hFibres:(A `&` F @^-1` [set y]) `<=` \bigcup_i (C i `&` F @^-1` [set y]).
  move=>x [hx hFx]; have [i _ hxi]:=hCover x hx.
  exists i=>//; by split.
have hBound:=@measure_indexed_cover R X [the choiceType of (nat:Type)] nu hn
  _ setT (fun i=>C i `&` F @^-1` [set y]) (countableP _) hFibres.
have hSum:nonnegative_sum setT (fun i=>nu (C i `&` F @^-1` [set y]))=0.
  apply:nonnegative_sum_zero=>i _; exact:hy i Logic.I.
rewrite hSum in hBound; apply/eqP; rewrite eq_le hBound /=.
exact (@measure_nonnegative R X nu hn (A `&` F @^-1` [set y])).
Qed.
