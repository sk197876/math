(** Federer (1969), 3.2.14, p. 252: for finite
    mass and closed-set measurability, rectifiability
    is equivalent to arbitrary-error approximation by
    one rectifiable set. E itself need not be measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP
  MeasureAlmostBasic MeasureFiniteClosure MeasureRestriction
  MeasureContinuityAbove ExtendedRealOrderLimit ExtendedRealReciprocalBounds
  RectifiableSetUP RectifiableElementary CountablyRectifiableUnions
  RectifiableClosedExhaustion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_rectifiable_finite_approximation]:
    the forward approximation observation of Federer
    3.2.14, p. 252. Approximation is by a closed
    rectifiable set, without requiring F to lie in E. *)
Theorem measure_rectifiable_finite_approximation (R : realType)
    (X : metricType R) (phi : set X -> \bar R) m (E : set X) :
  (forall C, closed C -> measure_measurable phi C) ->
  is_measure_m_rectifiable phi m E ->
  forall e : R, (0<e)%R -> exists F,
    closed F /\ is_m_rectifiable m F /\ phi (E `\` F)<e%:E.
Proof.
move=> hclosed [[hm [S [hS hES]]] hfin] e he.
have [F [hF [hinc hcover]]] := rectifiable_closed_increasing_cover hS.
pose nu := measure_restrict phi E.
have hnu : is_measure nu := measure_restrict_is_measure hm E.
pose D n := ~` F n.
have hD n : measure_measurable nu (D n).
  apply: measure_restrict_measurable.
  exact: measure_measurable_complement (hclosed _ (hF n).1).
have hmono n k : (n<=k)%N -> D k `<=` D n.
  move=> hnk x hx hFn; apply: hx; exact: hinc n k hnk x hFn.
have hDfin : nu (D 0%N)< +oo.
  apply: le_lt_trans _ hfin; apply: (@measure_mono R X phi hm)=> x [hx _]; exact hx.
have hnull : nu (\bigcap_n D n)=0.
  change (phi (E `&` (\bigcap_n D n))=0).
  apply: (@measure_null_subset R X phi hm (E `&` (\bigcap_n D n)) (E `\` S)).
  - move=> x [hx hDall]; split=> // hSx.
    have [n _ hFx] := hcover x hSx; exact: hDall n I hFx.
  - exact hES.
have hl := (measure_continuity_above hnu hD hmono hDfin).2.2.
rewrite hnull in hl.
have heE : 0<e%:E by rewrite lte_fin.
have [N hN] := hl e%:E heE.
exists (F N); split; first exact: (hF N).1.
split; first exact: (hF N).2.
exact: hN N (leqnn N).
Qed.

(** Source for [finite_approximation_measure_rectifiable]:
    the reverse approximation observation of Federer
    3.2.14, p. 252. The approximants need not be
    subsets of E or measurable. *)
Theorem finite_approximation_measure_rectifiable (R : realType)
    (X : metricType R) (phi : set X -> \bar R) m (E : set X) :
  is_measure phi -> phi E< +oo ->
  (forall e : R, (0<e)%R -> exists F,
    is_m_rectifiable m F /\ phi (E `\` F)<e%:E) ->
  is_measure_m_rectifiable phi m E.
Proof.
move=> hm hfin happ.
have hex n : exists F, is_m_rectifiable m F /\
    phi (E `\` F)<((n.+1%:R : R)^-1)%:E.
  apply: happ; by rewrite invr_gt0 ltr0n.
have [F hF] := choice hex.
pose S := \bigcup_n F n.
have hS : is_countably_m_rectifiable m S.
  apply: countably_rectifiable_countable_union (countableP setT) _=> n _.
  exact: rectifiable_countably_rectifiable (hF n).1.
split; last exact hfin.
split; first exact hm.
exists S; split=> //.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
apply: (@extended_real_reciprocal_upper_bound R (phi (E `\` S)) 0%R)=> n.
rewrite add0r; apply: le_trans _ (ltW (hF n).2).
apply: (@measure_mono R X phi hm)=> x [hx hnot]; split=> // hFn.
apply: hnot; by exists n.
Qed.

(** Source for [measure_rectifiable_iff_finite_approximation]:
    the complete equivalence in Federer 3.2.14,
    p. 252, with exactly finite mass, a measure
    and measurability of every closed set. *)
Theorem measure_rectifiable_iff_finite_approximation (R : realType)
    (X : metricType R) (phi : set X -> \bar R) m (E : set X) :
  is_measure phi -> phi E< +oo ->
  (forall C, closed C -> measure_measurable phi C) ->
  (is_measure_m_rectifiable phi m E <->
    forall e : R, (0<e)%R -> exists F,
      is_m_rectifiable m F /\ phi (E `\` F)<e%:E).
Proof.
move=> hm hfin hclosed; split.
- move=> hE e he.
  have [F [_ hF]] := measure_rectifiable_finite_approximation hclosed hE he.
  by exists F.
- exact: finite_approximation_measure_rectifiable hm hfin.
Qed.
