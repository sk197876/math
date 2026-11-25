(** Federer (1969), 3.2.14, p. 252, final
    existence assertion: a finite-mass set has a
    countably rectifiable Borel part whose complement
    is purely unrectifiable. Maximize the original
    measure restricted to A, without assuming A measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureRestriction
  MeasureFiniteClosure MeasurableBorelFamily BorelFamilyUP BorelFamilyBasic TopologicalBorel
  RectifiableSetUP RectifiableElementary RectifiableClosure CountablyRectifiableUnions
  FiniteMeasureFamilyMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_pure_borel_decomposition]:
    the complete last existence assertion of Federer
    3.2.14, p. 252. B is countably m rectifiable
    and Borel; A minus B is purely (phi,m) unrectifiable.
    Neither measurability of A nor B contained in A
    is imposed. *)
Theorem rectifiable_pure_borel_decomposition (R : realType)
    (X : metricType R) (phi : set X -> \bar R) m (A : set X) :
  is_measure phi -> phi A< +oo ->
  (forall C, closed C -> measure_measurable phi C) ->
  exists B, borel_set B /\ is_countably_m_rectifiable m B /\
    is_purely_measure_m_unrectifiable phi m (A `\` B).
Proof.
move=> hm hfin hclosed.
pose nu := measure_restrict phi A.
have hnu : is_measure nu := measure_restrict_is_measure hm A.
have hnuT : nu setT< +oo by rewrite /nu /measure_restrict setIT.
pose C := [set B : set X | borel_set B /\ is_countably_m_rectifiable m B].
have hex : exists B, C B.
  exists set0; split; [exact: open_borel_set open0|exact: countably_rectifiable_empty].
have hCunion (F : nat -> set X) : (forall n, C (F n)) -> C (\bigcup_n F n).
  move=> hF; split.
  - exact: (@borel_set_countable_union X [the choiceType of (nat : Type)]
      setT F (countableP setT) (fun n _ => (hF n).1)).
  - exact: (@countably_rectifiable_countable_union R X [the choiceType of (nat : Type)]
      m setT F (countableP setT) (fun n _ => (hF n).2)).
have [B [[hBb hBr] hmax]] := finite_measure_countable_union_maximum hnu hnuT hex hCunion.
have hBmeas : measure_measurable nu B.
  apply: measure_restrict_measurable.
  apply: (open_measurable_implies_borel_measurable hm _ hBb).
  move=> U hU; have hh := measure_measurable_complement (hclosed _ (open_closedC hU)).
  by rewrite setCK in hh.
have hfinite D : nu D \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X nu hnu D).
  apply: le_lt_trans _ hnuT; apply: (@measure_mono R X nu hnu)=> x hx; exact I.
have hval D : nu D=(fine (nu D))%:E by rewrite fineK //; exact: hfinite.
exists B; split=> //; split=> //; split; first exact hm.
move=> [F [hFA [hF hpos]]].
pose K := closure F.
have hKr : is_m_rectifiable m K := rectifiable_closure hF.
have hKb : borel_set K := closed_borel_set (@closed_closure X F).
have hCK : C (B `|` K).
  split.
  - exact (@borel_family_binary_union X setT
      (@borel_set X) (borel_sets_family X) B K hBb hKb).
  - exact: countably_rectifiable_binary_union hBr (rectifiable_countably_rectifiable hKr).
have hmval := hmax (B `|` K) hCK.
have hI : (B `|` K) `&` B=B.
  apply/seteqP; split=> x; first by move=> [_ hx].
  by move=> hx; split; first left.
have hD : (B `|` K) `\` B=K `\` B.
  apply/seteqP; split=> x.
  - move=> [[hx|hx] hn]; first by exfalso; exact: hn hx.
    by split.
  - move=> [hx hn]; split=> //; by right.
have hs := hBmeas (B `|` K); rewrite hI hD in hs.
rewrite hs (hval B) (hval (K `\` B)) -EFinD lee_fin in hmval.
have hd0 : (fine (nu (K `\` B))<=0)%R.
  have hh : (fine (nu B)+fine (nu (K `\` B))<=fine (nu B)+0)%R by rewrite addr0.
  by rewrite lerD2l in hh.
have hz : nu (K `\` B)=0.
  apply/eqP; rewrite eq_le (measure_nonnegative hnu) andbT (hval (K `\` B)) lee_fin.
  exact hd0.
have hnull : phi F=0.
  apply: (@measure_null_subset R X phi hm F (A `&` (K `\` B)))=> // x hx.
  have [hAx hn] := hFA x hx; split=> //; split=> //; exact: subset_closure hx.
by rewrite hnull ltxx in hpos.
Qed.
