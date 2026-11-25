(** Federer (1969), proof of 2.8.7, p. 144: the disjoint selection inside an
    open set of finite measure covers almost all of its intersection with
    the target. We retain Federer's target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover MeasureDisjointSupport
  NonnegativeSum NonnegativeFamilyTails CoveringFamilyUP CoveringFamilyLaws
  WeightedCoverSelectionUP WeightedCoverSelection WeightedEnlargements
  FiniteRemainderEnlargements FineCoverOpenRestriction EnlargementMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_open_enlargement_adequacy]: the local selection and
    vanishing remainder in Federer 2.8.7, p. 144 The testing open W has
    finite measure; the target A need not be measurable or have finite
    measure. Strict enlargement control supplies positive selected measures
    and hence countability. Finite-removal covers and small sum tails give
    the null remainder. *)
Theorem finite_open_enlargement_adequacy (R : realType) (X : metricType R)
    (F : set (set X)) (mu : set X -> \bar R)
    (d : set X -> R) (tau lambda : R) (A : set X) :
  is_covering_theory_context F mu ->
  (forall S, F S -> (0 <= d S)%R) ->
  (exists C, forall S, F S -> (d S <= C)%R) -> (1 < tau)%R -> (1 < lambda)%R ->
  (forall S, F S -> mu (weighted_enlargement F d tau S) < lambda%:E * mu S) ->
  family_covers_finely F A -> forall W, open W -> mu W < +oo ->
  exists G, is_adequate_cover_selection mu F A W G.
Proof.
move=> hc hnon hbounded ht hl hbound hf W hW hWf.
pose hm := covering_context_measure hc.
pose P := family_members_within F W.
have hPF : P `<=` F by move=> S [].
have hposF S (hS : F S) : 0 < mu S.
  exact (@strict_enlargement_bound_positive R X mu hm F d tau lambda S (hbound S hS)).
have hnonempty S (hS : P S) : S <> set0.
  move=> he; have hp := hposF S hS.1.
  by rewrite he (measure_empty hm) ltxx in hp.
have hnonP S (hS : P S) : (0 <= d S)%R := hnon S hS.1.
have hboundedP : exists C, forall S, P S -> (d S <= C)%R.
  have [C hC] := hbounded; exists C=> S hS; exact: hC S hS.1.
pose G := @weighted_cover_selection R X P d tau hnonempty hnonP hboundedP ht.
have hG : is_weighted_cover_selection P d tau G.
  exact: weighted_cover_selection_specification.
have hGP S (hS : G S) : P S := @weighted_selection_members R X P d tau G hG S hS.
have hGF S (hS : G S) : F S := (hGP S hS).1.
have hwithin S (hS : G S) : S `<=` W := (hGP S hS).2.
have hmeas S (hS : G S) : measure_measurable mu S.
  exact (@covering_context_member_measurable R X F mu hc S (hGF S hS)).
have hdis := @weighted_selection_disjoint R X P d tau G hG.
have hcount : countable G.
  have h := @measure_disjoint_positive_countable R X [the choiceType of set X]
    mu hm W G idfun hWf hwithin hmeas hdis.
  have he : G `&` [set S | 0 < mu S] = G.
    apply/seteqP; split; first by move=> S [].
    move=> S hS; split=> //; exact: hposF S (hGF S hS).
  by rewrite he in h.
have hl0 : (0 <= lambda)%R := ltW (lt_trans ltr01 hl).
have hsum := @enlargement_selection_sum_bound R X mu hm F G d tau lambda W
  hdis hmeas hwithin hl0 (fun S hS => ltW (hbound S (hGF S hS))).
have hWfin : mu W \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm W)).
have hsumf : nonnegative_sum G (fun S => mu (weighted_enlargement F d tau S)) < +oo.
  apply: le_lt_trans hsum _.
  rewrite -(fineK hWfin) -EFinM; exact: ltry.
have hfP : family_covers_finely P (W `&` A).
  exact (@fine_cover_open_restriction R X F A W hW hf).
have hclosedP S (hS : P S) : closed S.
  exact (@covering_context_closed R X F mu hc S hS.1).
pose U := \bigcup_(S in G) S.
have hcover H (hH : finite_set H) (hHG : H `<=` G) :
    ((W `&` A) `\` U) `<=` \bigcup_(S in G `\` H) weighted_enlargement F d tau S.
  move=> x [hx hn].
  have hr : ((W `&` A) `\` \bigcup_(S in H) S) x.
    split=> //; move=> [S hS hs]; apply: hn.
    exists S; first exact: hHG S hS.
    exact hs.
  have [S hS hxS] := @weighted_selection_finite_remainder_cover R X P d tau G (W `&` A)
    hclosedP hfP hG H hH hHG x hr.
  exists S=> //.
  exact (@weighted_enlargement_mono_family R X P F d tau S hPF x hxS).
exists G; constructor.
- exact hGF.
- exact hcount.
- exact hdis.
- move=> x [S hS hx]; exact: hwithin S hS x hx.
- have hrf : mu ((W `&` A) `\` U) \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm _)).
    apply: le_lt_trans (@measure_mono R X mu hm _ W _) hWf.
    by move=> x [[hw _] _].
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt; apply/negP=> hp.
  pose e := fine (mu ((W `&` A) `\` U)).
  have he : (0 < e)%R by move: hp; rewrite -(fineK hrf) lte_fin.
  have [H [hHG [hH htiny]]] := @nonnegative_family_small_tail R [the choiceType of set X]
    G (fun S => mu (weighted_enlargement F d tau S)) e
    (fun S _ => measure_nonnegative hm _) hsumf he.
  have hct : countable (G `\` H).
    have hs : G `\` H `<=` G by move=> S [].
    exact: sub_countable (subset_card_le hs) hcount.
  have hb := @measure_indexed_cover R X [the choiceType of set X] mu hm
    ((W `&` A) `\` U) (G `\` H) (weighted_enlargement F d tau)
    hct (hcover H hH hHG).
  have hbad := le_lt_trans hb htiny.
  by rewrite /e fineK // ltxx in hbad.
Qed.
