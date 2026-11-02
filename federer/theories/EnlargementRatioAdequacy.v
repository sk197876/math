(** The application of 2.8.7 in Federer (1969), 2.8.17, pp. 151–152. Here
    positivity on the original family follows the Federer erratum, p. 3,
    book p. 151 line 24. Source context: EnlargementRatio.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic CoveringFamilyUP CoveringFamilyLaws
  CoveringRelationUP CoveringRelationFineness CoveringRelationLimits CoveringRelationCutoffs
  PartialFunctionUP FamilyWeightedEnlargements WeightedEnlargements EnlargementRatio EnlargementAdequacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [enlargement_ratio_cutoff_adequate]: the assertion that
    C_n(A_n) is adequate for A_n in Federer 2.8.17, p. 152 This supporting
    statement isolates an arbitrary cutoff lambda>1 and target A. The weight
    is still defined on F; a total extension is used only through its
    agreement laws. *)
Theorem enlargement_ratio_cutoff_adequate (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (F : set (set X))
    (delta : {S : set X | F S} -> R) (tau lambda : R)
    (V C : X -> set X -> Prop) (A : set X) :
  is_covering_theory_context F phi ->
  (forall x S, V x S -> F S) -> (forall x S, C x S -> V x S) ->
  is_covering_relation C -> (forall x, A x -> covering_relation_fine_at C x) ->
  (forall S, (0 <= delta S)%R) ->
  (forall S, F S -> metric_set_bounded S) -> (forall S, F S -> 0 < phi S) ->
  (1 < tau)%R -> (1 < lambda)%R ->
  (forall x, A x -> covering_upper_limit V (family_enlargement_ratio_function phi delta tau) x < lambda%:E) ->
  family_is_measure_adequate phi
    (covering_relation_image (covering_value_cutoff C (family_enlargement_ratio_function phi delta tau) lambda%:E) A) A.
Proof.
move=> hc hVF hCV hC hf hnon hbounded hpos ht hl hlim.
pose f := family_enlargement_ratio_function phi delta tau.
pose Q := covering_value_cutoff C f lambda%:E.
pose H := covering_relation_image Q A.
have hHF : H `<=` F.
  move=> S [x [_ [hx _]]]; exact: hVF x S (hCV x S hx).
have hhc := @covering_context_subfamily R X phi F H hc hHF.
have hdom x S : V x S -> partial_function_domain f S.
  move=> hx; exists (family_enlargement_ratio_value phi delta tau (exist F S (hVF x S hx))).
  exact (@family_enlargement_ratio_graph R X phi F delta tau (exist F S (hVF x S hx))).
have hQfine x : A x -> covering_relation_fine_at Q x.
  move=> hx; exact (@covering_value_cutoff_fine R X C V f x lambda%:E
    (hCV x) (hdom x) (hf x hx) (hlim x hx)).
have hQcover : is_covering_relation Q by move=> x S [hx _]; exact: hC x S hx.
have hHfine := @covering_relation_fine_image_cover R X Q A hQcover hQfine.
have [d hd] := @family_weight_extension_exists R X F delta.
have hdnon S (hS : F S) : (0 <= d S)%R by rewrite (hd S hS); exact: hnon.
have hbound S : H S -> (d S < lambda)%R /\ phi (weighted_enlargement F d tau S) < lambda%:E * phi S.
  move=> hS.
  have hSF := hHF S hS.
  have [x [_ [_ [y [hy hyb]]]]] := hS.
  have hgraph := @family_enlargement_ratio_graph R X phi F delta tau (exist F S hSF).
  have hey := partial_function_single_valued hy hgraph.
  rewrite hey (@family_enlargement_ratio_extension R X phi F delta d tau hd (exist F S hSF)) in hyb.
  have hfinite : phi S \is a fin_num.
    by rewrite (ge0_fin_numE (measure_nonnegative (covering_context_measure hc) S));
      exact (@covering_context_bounded_finite R X F phi hc S (hbounded S hSF)).
  have he : phi S = (fine (phi S))%:E := esym (fineK hfinite).
  have hq : (0 < fine (phi S))%R by have := hpos S hSF; rewrite he lte_fin.
  have [hw hm] := @nonnegative_enlargement_ratio_bound R (d S) (fine (phi S)) lambda
    (phi (weighted_enlargement F d tau S)) (hdnon S hSF) hq
    (measure_nonnegative (covering_context_measure hc) _) hyb.
  split=> //; by rewrite he.
have hnH S (hS : H S) : (0 <= d S)%R := hdnon S (hHF S hS).
have hbH : exists M, forall S, H S -> (d S <= M)%R.
  exists lambda=> S hS; exact: ltW (hbound S hS).1.
have heH S (hS : H S) : phi (weighted_enlargement H d tau S) < lambda%:E * phi S.
  apply: le_lt_trans (@measure_mono R X phi (covering_context_measure hc) _ _
    (@weighted_enlargement_mono_family R X H F d tau S hHF)) _.
  exact: (hbound S hS).2.
exact (@enlargement_control_adequacy R X H phi d tau lambda A hhc hnH hbH ht hl heH hHfine).
Qed.
