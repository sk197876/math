(** Federer (1969), 3.3.15, p. 299: countable unions
    of the original pure pieces remain purely unrectifiable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RectifiableSetUP RectifiableElementary PureUnrectifiableLaws
  MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pure_unrectifiable_countable_union]: supporting the
    last paragraph of Federer 3.3.15, p. 299. Every actual rectifiable
    subset of the original countable union is covered by its null
    rectifiable intersections with the original pure pieces. Neither
    the original pieces nor their intersections need be measurable. *)
Lemma pure_unrectifiable_countable_union (R:realType) (X:metricType R) m
    (phi:set X->\bar R) (J:choiceType) (D:set J) (A:J->set X):
  is_measure phi ->countable D ->
  (forall j,D j ->is_purely_measure_m_unrectifiable phi m (A j)) ->
  is_purely_measure_m_unrectifiable phi m (\bigcup_(j in D) A j).
Proof.
move=>hPhi hD hPure.
apply/(pure_unrectifiable_iff_rectifiable_subsets_null); split; first exact:hPhi.
move=>F hFSub hRect.
pose C j:=F `&` A j.
have hNull j:D j ->phi (C j)=0.
  move=>hj.
  have hSubset:C j `<=` A j by move=>x [_ hx].
  have hRectC:is_m_rectifiable m (C j).
    apply:rectifiable_subset _ hRect; by move=>x [hx _].
  exact:((@pure_unrectifiable_iff_rectifiable_subsets_null R X phi m (A j)).1 (hPure j hj)).2 (C j) hSubset hRectC.
have hUnionNull:=@measure_null_countable_union R X J phi hPhi D C hD hNull.
apply:(@measure_null_subset R X phi hPhi F (\bigcup_(j in D) C j) _ hUnionNull).
move=>x hx; have [j hj hAx]:=hFSub x hx.
exists j; first exact:hj.
by split.
Qed.

(** Source for [pure_unrectifiable_dominated_on_source]: supporting
    the purity transfer in the last sentence of Federer 3.3.15,
    p. 299. On every original rectifiable subset of the source,
    domination by a pure measure forces original outer mass zero.
    The measure comparison is separate from the pure-set conclusion. *)
Lemma pure_unrectifiable_dominated_on_source (R:realType) (X:metricType R) m
    (phi psi:set X->\bar R) (A:set X):
  is_measure phi ->is_purely_measure_m_unrectifiable psi m A ->
  (forall F,F `<=` A ->phi F<=psi F) ->
  is_purely_measure_m_unrectifiable phi m A.
Proof.
move=>hPhi hPure hDomination.
apply/(pure_unrectifiable_iff_rectifiable_subsets_null); split; first exact:hPhi.
move=>F hFA hRect.
have hPsiZero:=((@pure_unrectifiable_iff_rectifiable_subsets_null R X psi m A).1 hPure).2 F hFA hRect.
have hBound:=hDomination F hFA; rewrite hPsiZero in hBound.
apply/eqP; rewrite eq_le (measure_nonnegative hPhi) andbT.
exact:hBound.
Qed.
