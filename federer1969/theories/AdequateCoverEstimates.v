(** Federer (1969), 2.8.1, p. 142, motivation after the definitions: sums of
    the measures of selected sets give an upper estimate for the covered
    target and a lower estimate for a containing neighborhood when the
    selected sets are disjoint. These statements are proved for the actual
    selected family, including infinite sums and nonmeasurable targets.
    Source context: CoveringFamilyUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic
  MeasureSplit MeasureCountableAdditivity CountablyClosedFamilyUP
  CoveringFamilyUP CoveringFamilyLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [adequate_selection_target_bound]: the upper
    estimate explained in Federer 2.8.1, p. 142: a countable
    covering outside a null remainder gives mu(V intersect A)
    at most the sum of mu(B) over the selected sets. *)
Lemma adequate_selection_target_bound (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : set (set X)) (A V : set X) (G : set (set X)) :
  is_adequate_cover_selection mu F A V G ->
  mu (V `&` A) <= nonnegative_sum G mu.
Proof.
move=> hG.
have hcov : V `&` A `<=`
    (\bigcup_(B in G) B) `|` ((V `&` A) `\` \bigcup_(B in G) B).
  move=> x hx; case: (pselect ((\bigcup_(B in G) B) x))=> h.
  - by left.
  - right; by split.
have hb := @measure_binary_cover R X mu hm _ _ _ hcov.
rewrite (adequate_selection_remainder hG) adde0 in hb.
apply: le_trans hb _.
exact (@measure_countable_cover R X mu hm _ G
  (adequate_selection_countable hG) (fun x hx => hx)).
Qed.

(** Source for [adequate_selection_neighborhood_bound]: the
    lower estimate explained in Federer 2.8.1, p. 142:
    for measurable disjoint selected sets contained in V,
    their measure sum is at most mu(V). No finiteness of
    mu(V) is assumed. *)
Lemma adequate_selection_neighborhood_bound (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : set (set X)) (A V : set X) (G : set (set X)) :
  (forall B, F B -> measure_measurable mu B) ->
  is_adequate_cover_selection mu F A V G ->
  nonnegative_sum G mu <= mu V.
Proof.
move=> hF hG.
have hmeas : forall B, G B -> measure_measurable mu B.
  move=> B hB; exact: hF _ (adequate_selection_members hG hB).
have hd : forall B C, G B -> G C -> B != C ->
    forall x, B x -> C x -> False.
  move=> B C hB hC hBC x hx hy.
  have hne : B <> C by move=> he; move: hBC; by rewrite he eqxx.
  have hzero := @adequate_selection_disjoint R X mu F A V G hG B C hB hC hne.
  have hh : (B `&` C) x by split.
  by rewrite hzero in hh.
have he := @measure_countable_disjoint_additivity R X [the choiceType of set X]
  mu hm G idfun (adequate_selection_countable hG) hmeas hd.
rewrite -he.
exact (@measure_mono R X mu hm (\bigcup_(B in G) B) V (adequate_selection_within hG)).
Qed.

(** Source for [adequate_family_measure_estimates]: combines
    the two estimates in the motivation of Federer 2.8.1,
    p. 142, for each open neighborhood. Closedness and
    open-set measurability imply measurability of selected
    members. Bounded-set finiteness is not needed here. *)
Theorem adequate_family_measure_estimates (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X)) (A : set X) :
  is_covering_theory_context F mu -> family_is_measure_adequate mu F A ->
  forall V, open V -> exists G,
    is_adequate_cover_selection mu F A V G /\
    mu (V `&` A) <= nonnegative_sum G mu /\ nonnegative_sum G mu <= mu V.
Proof.
move=> hc hf V hV; have [G hG] := hf V hV; exists G; split=> //; split.
- exact (@adequate_selection_target_bound R X mu (covering_context_measure hc)
    F A V G hG).
- exact (@adequate_selection_neighborhood_bound R X mu (covering_context_measure hc)
    F A V G (@covering_context_member_measurable R X F mu hc) hG).
Qed.

(** Source for [adequate_family_almost_cover]: the case V=X
    of Federer 2.8.1, p. 142: adequacy produces a countable
    disjointed subfamily covering almost all of A, including
    when A itself is not measurable. *)
Theorem adequate_family_almost_cover (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X)) (A : set X) :
  family_is_measure_adequate mu F A -> exists G,
    G `<=` F /\ countable G /\ set_family_disjoint G /\
    mu (A `\` \bigcup_(B in G) B) = 0.
Proof.
move=> hf; have [G hG] := hf setT openT; exists G.
split; first exact: adequate_selection_members hG.
split; first exact: adequate_selection_countable hG.
split; first exact: adequate_selection_disjoint hG.
have h := adequate_selection_remainder hG; by rewrite setTI in h.
Qed.

(** Source for [adequate_family_neighborhood_estimates]: the
    actual neighborhood estimate described in Federer 2.8.1,
    p. 142. If the open V contains A, the selected measure
    sum lies between mu(A) and mu(V), without assuming that
    A itself is measurable. *)
Corollary adequate_family_neighborhood_estimates (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X)) (A V : set X) :
  is_covering_theory_context F mu -> family_is_measure_adequate mu F A ->
  open V -> A `<=` V -> exists G,
    is_adequate_cover_selection mu F A V G /\
    mu A <= nonnegative_sum G mu /\ nonnegative_sum G mu <= mu V.
Proof.
move=> hc hf hV hAV.
have [G [hG [hlo hhi]]] := @adequate_family_measure_estimates R X mu F A hc hf V hV.
have he : V `&` A = A.
  apply/seteqP; split=> [x [_ hx]|x hx]; first exact hx.
  by split; first exact: hAV.
rewrite he in hlo; exists G; by split=> //; split.
Qed.
