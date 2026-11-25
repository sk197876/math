(** Federer (1969), 3.2.31, p. 269: supporting countable
    source-chart assembly of the positive fibre locus. A
    source remainder with almost everywhere null fibres adds
    only a null target remainder. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  RectifiableSetUP CountablyMeasureRectifiableOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_positive_fibre_locus_rectifiable]: supporting
    countable-compact-source reduction in Federer 3.2.31, p. 269.
    Positive fibres of each chart already have countable measure
    rectifiability. Countable subadditivity and the independently
    proved null remainder imply the same for the original source.
    Neither source disjointness nor measurable fibres are assumed. *)
Theorem countable_positive_fibre_locus_rectifiable (R:realType) (X:choiceType) (Y:metricType R)
    (nu:set X->\bar R) (beta:set Y->\bar R) (hn:is_measure nu) (hb:is_measure beta)
    (F:X->Y) (W:set X) (C:nat->set X) mu:
  (forall i,is_countably_measure_m_rectifiable beta mu [set y|0<nu (C i `&` F @^-1` [set y])]) ->
  measure_almost_everywhere beta
    [set y|nu ((W `\` \bigcup_i C i) `&` F @^-1` [set y])=0] ->
  is_countably_measure_m_rectifiable beta mu [set y|0<nu (W `&` F @^-1` [set y])].
Proof.
move=>hC hR.
pose A:=W `\` \bigcup_i C i.
pose N:=~` [set y:Y|nu (A `&` F @^-1` [set y])=0].
have hN:beta N=0:=hR.
pose Q j:set Y:=if j is i.+1 then [set y|0<nu (C i `&` F @^-1` [set y])] else N.
have hQ j:is_countably_measure_m_rectifiable beta mu (Q j).
  case:j=>[|i]; last exact:hC.
  exact (@countably_measure_rectifiable_null R Y beta mu N hb hN).
have hUnion:=@countably_measure_rectifiable_countable_union R Y [the choiceType of (nat:Type)]
  beta mu setT Q hb (countableP _) (fun j _=>hQ j).
apply:(countably_measure_rectifiable_subset _ hUnion)=>y hy.
change (is_true (0<nu (W `&` F @^-1` [set y]))) in hy.
case:(pselect (nu (A `&` F @^-1` [set y])=0))=>hAy; last by exists 0%N.
case:(pselect (exists i,0<nu (C i `&` F @^-1` [set y])))=>[[i hi]|hNo]; first by exists i.+1.
have hPiece i:nu (C i `&` F @^-1` [set y])=0.
  apply/eqP; rewrite eq_le (measure_nonnegative hn) andbT leNgt; apply/negP=>h.
  apply:hNo; by exists i.
have hPieces:nu (\bigcup_i (C i `&` F @^-1` [set y]))=0.
  apply:(measure_null_countable_union hn (countableP _))=>i _; exact:hPiece.
have hTotal:nu ((A `&` F @^-1` [set y]) `|` \bigcup_i (C i `&` F @^-1` [set y]))=0.
  exact (measure_null_union hn hAy hPieces).
have hNull:nu (W `&` F @^-1` [set y])=0.
  apply:(measure_null_subset hn _ hTotal)=>x [hx hFx].
  case:(pselect ((\bigcup_i C i) x))=>[[i _ hxi]|hNot].
  - right; exists i=>//; by split.
  - left; split=>//; by split.
by move:hy; rewrite hNull ltxx.
Qed.
