(** Federer (1969), 2.8.2, pp. 142–143: finite disjoint selections retaining
    a strict contraction. Targets need not be measurable; only their outer
    measure must be finite at this stage. The square-root factor is exactly
    Federer's. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure
  MeasureRestriction CountablyClosedFamilyUP RecurrentContraction
  ContractionCoverUP FiniteSubfamilyApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [empty_contraction_cover_selection]: the null-error case in
    the finite selection of Federer 2.8.2, pp. 142–143, explicitly
    separated. Choose no sets when mu(W intersect A)=0. *)
Lemma empty_contraction_cover_selection (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X)) (A W : set X) (q : R) :
  mu (W `&` A) = 0 -> is_contraction_cover_selection mu F A W q set0.
Proof.
move=> hz; constructor.
- by move=> B [].
- by move=> B C [].
- by move=> x [B []].
- have he : ((W `&` A) `\` \bigcup_(B in (@set0 (set X))) B) = W `&` A.
    apply/seteqP; split=> [x [hx _]|x hx]; first exact hx.
    split=> //; by move=> [B []].
  by rewrite he hz mule0.
Qed.

(** Source for [contraction_selection_subfamily_with_bound]:
    supporting inheritance of eligibility, disjointness and
    containment when H is reduced to a finite subfamily in
    Federer 2.8.2, p. 143. The new measure bound is a
    separate premise; it is not inherited by monotonicity. *)
Lemma contraction_selection_subfamily_with_bound (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X)) (A W : set X)
    (p q : R) (H G : set (set X)) :
  is_contraction_cover_selection mu F A W p H -> G `<=` H ->
  mu ((W `&` A) `\` \bigcup_(B in G) B) <= q%:E * mu (W `&` A) ->
  is_contraction_cover_selection mu F A W q G.
Proof.
move=> hH hGH hb; constructor.
- move=> B hB; exact (@contraction_selection_members R X mu F A W p H hH B (hGH B hB)).
- move=> B C hB hC hBC.
  exact (@contraction_selection_disjoint R X mu F A W p H hH
    B C (hGH B hB) (hGH C hC) hBC).
- move=> x [B hB hx]; apply: (@contraction_selection_within R X mu F A W p H hH x).
  by exists B; first exact: hGH.
- exact hb.
Qed.

(** Source for [finite_contraction_cover_selection]: the selection of a
    finite G_j with square-root contraction in Federer 2.8.2, pp. 142–143
    Continuity from above is applied to mu restricted to A, so the target A
    is not assumed measurable. *)
Theorem finite_contraction_cover_selection (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (F : set (set X))
    (A : set X) (sigma : R) :
  (forall B, F B -> closed B) ->
  (forall V, open V -> measure_measurable mu V) ->
  mu A < +oo -> (0 < sigma < 1)%R ->
  has_local_cover_contraction mu F A sigma ->
  forall W, open W -> exists G,
    finite_set G /\ is_contraction_cover_selection mu F A W (Num.sqrt sigma) G.
Proof.
move=> hF hopen hAf hsigma hlocal W hW.
case: (pselect (mu (W `&` A) = 0))=> [hz|hnz].
- exists set0; split; first exact: finite_set0.
  exact (@empty_contraction_cover_selection R X mu F A W (Num.sqrt sigma) hz).
- have [H [hH hsel]] := hlocal W hW.
  have hnon := @measure_nonnegative R X mu hm (W `&` A).
  have hne : mu (W `&` A) != 0 by apply/eqP.
  have hpos : 0 < mu (W `&` A) by rewrite lt_neqAle eq_sym hne hnon.
  have hf : mu (W `&` A) < +oo.
    apply: le_lt_trans (@measure_mono R X mu hm _ A _) hAf.
    by move=> x [].
  have hfin : mu (W `&` A) \is a fin_num by rewrite (ge0_fin_numE hnon).
  have hrealpos : (0 < fine (mu (W `&` A)))%R.
    by move: hpos; rewrite -(fineK hfin) lte_fin.
  have hroot := @covering_contraction_root_bounds R sigma hsigma.
  have hstrict : sigma%:E * mu (W `&` A) < (Num.sqrt sigma)%:E * mu (W `&` A).
    rewrite -(fineK hfin) -!EFinM lte_fin (ltr_pM2r hrealpos).
    exact hroot.2.
  have herr := le_lt_trans (contraction_selection_bound hsel) hstrict.
  pose nu := measure_restrict mu A.
  have hnu : is_measure nu := @measure_restrict_is_measure R X mu hm A.
  have hWm : measure_measurable nu W.
    exact (@measure_restrict_measurable R X mu A W (hopen W hW)).
  have hWf : nu W < +oo by rewrite /nu /measure_restrict (setIC A W).
  have hBm : forall B, H B -> measure_measurable nu B.
    move=> B hB.
    have hclosed := hF B (@contraction_selection_members R X mu F A W sigma H hsel B hB).
    have h := measure_measurable_complement (hopen _ (closed_openC hclosed)).
    have hmB : measure_measurable mu B by rewrite setCK in h.
    exact (@measure_restrict_measurable R X mu A B hmB).
  have hset S : A `&` (W `\` S) = (W `&` A) `\` S.
    apply/seteqP; split.
    - by move=> x [ha [hw hn]]; split=> //; split.
    - by move=> x [[hw ha] hn]; split=> //; split.
  have hnerr : nu (W `\` \bigcup_(B in H) B) <
      (Num.sqrt sigma)%:E * mu (W `&` A).
    by rewrite /nu /measure_restrict hset.
  have [G [hGH [hGf hGe]]] := @finite_subfamily_measure_error R X nu hnu W H
    ((Num.sqrt sigma)%:E * mu (W `&` A)) hWm hWf hH hBm hnerr.
  exists G; split=> //.
  apply: (@contraction_selection_subfamily_with_bound R X mu F A W
    sigma (Num.sqrt sigma) H G hsel hGH).
  apply: ltW; by move: hGe; rewrite /nu /measure_restrict hset.
Qed.

(** Source for [finite_selection_open_remainder]: finite
    unions of the selected closed sets have open complements,
    ensuring that the induction continues in Federer 2.8.2,
    pp. 142–143. This uses only background finite-union topology. *)
Lemma finite_selection_open_remainder (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X)) (A W : set X)
    (q : R) (G : set (set X)) :
  (forall B, F B -> closed B) -> finite_set G ->
  is_contraction_cover_selection mu F A W q G -> open W ->
  open (W `\` \bigcup_(B in G) B).
Proof.
move=> hF hGf hG hW.
have hclosed : closed (\bigcup_(B in G) B).
  apply: (@closed_bigcup X [the choiceType of set X] G idfun hGf)=> B hB.
  exact: hF _ (@contraction_selection_members R X mu F A W q G hG B hB).
rewrite setDE; exact: openI hW (closed_openC hclosed).
Qed.
