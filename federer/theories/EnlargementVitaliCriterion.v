(** The complete corrected theorem of Federer (1969), 2.8.17, pp. 151–152.
    The May 1987 erratum, p. 3, book p. 151 line 24, adds positivity of phi
    on V(X); book p. 152 line 10 corrects the final reference to 2.8.3. We
    retain Federer's corrected hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  CoveringFamilyUP CoveringFamilyLaws CoveringRelationUP CoveringRelationFineness
  CoveringRelationLimits CoveringRelationCutoffs EnlargementRatio EnlargementRatioAdequacy
  AdequacyAlmostCover TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_8_17]: direct formalisation of the
    complete theorem in Federer 2.8.17, pp. 151–152,
    with both relevant erratum corrections cited in the header.
    The standing context, bounded closed members, everywhere
    fineness, nonnegative weight on V(X), strict tau>1,
    positivity on V(X), and almost-everywhere finite nonnegative
    upper ratio limit are retained. Cutoff levels n+2 are
    cofinal among positive integers and ensure lambda>1 when
    applying the original 2.8.7. No extra target regularity
    or separability is imposed. *)
Theorem federer_2_8_17 (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (delta : {S : set X | covering_relation_image V setT S} -> R) (tau : R) :
  is_covering_theory_context (covering_relation_image V setT) phi ->
  is_covering_relation V -> (forall x, covering_relation_fine_at V x) ->
  (forall S, covering_relation_image V setT S -> metric_set_bounded S) ->
  (forall S, covering_relation_image V setT S -> 0 < phi S) ->
  (forall S, (0 <= delta S)%R) -> (1 < tau)%R ->
  measure_almost_everywhere phi [set x |
    0 <= covering_upper_limit V (family_enlargement_ratio_function phi delta tau) x < +oo] ->
  is_vitali_relation phi V.
Proof.
move=> hc hV hf hbounded hpos hnon ht hgood.
pose F := covering_relation_image V setT.
pose f := family_enlargement_ratio_function phi delta tau.
pose L x := covering_upper_limit V f x.
have hVF x S : V x S -> F S by move=> hx; exists x.
constructor=> //.
- move=> S hS; exact: closed_borel_set (covering_context_closed hc hS).
- move=> C Z hCV hCfine.
  pose C0 := fun x S => C x S /\ Z x.
  pose A n := Z `&` [set x | 0 <= L x /\ L x < ((n+2)%:R : R)%:E].
  pose H := covering_relation_image C Z.
  have hHF : H `<=` F.
    move=> S [x [_ hx]]; exact: hVF x S (hCV x S hx).
  have hh := @covering_context_subfamily R X phi F H hc hHF.
  have hC0V x S : C0 x S -> V x S by move=> [hx _]; exact: hCV x S hx.
  have hC0cover : is_covering_relation C0.
    move=> x S hx; exact: hV x S (hC0V x S hx).
  have ha n : family_is_measure_adequate phi H (A n).
    have hlambda : (1 < (n+2)%:R :> R)%R by rewrite ltr1n addn2 !ltnS leq0n.
    have hAfine x : A n x -> covering_relation_fine_at C0 x.
      move=> [hx _]; apply: (@covering_relation_fine_mono R X C C0 x) (hCfine x hx).
      by move=> S hS; split.
    have hAlim x : A n x -> L x < ((n+2)%:R : R)%:E by move=> [_ []].
    have hcuta := @enlargement_ratio_cutoff_adequate R X phi F delta tau ((n+2)%:R : R)
      V C0 (A n) hc hVF hC0V hC0cover hAfine hnon hbounded hpos ht hlambda hAlim.
    apply: (@adequate_family_mono_family R X phi _ H (A n)) hcuta.
    move=> S [x [[hx _] [[hCS _] _]]]; by exists x.
  have hnull : phi (Z `\` \bigcup_(n in @setT nat) A n) = 0.
    apply: (@measure_null_subset R X phi (covering_context_measure hc) _
      (~` [set x | 0 <= L x < +oo])) hgood.
    move=> x [hx hn] /andP [h0 hfin].
    have hlf : L x \is a fin_num by rewrite (ge0_fin_numE h0).
    have hreal : (0 <= fine (L x))%R by move: h0; rewrite -(fineK hlf) lee_fin.
    pose n := Num.bound (fine (L x)).
    have hb : L x < (n%:R : R)%:E by rewrite -(fineK hlf) lte_fin; exact: archi_boundP hreal.
    have hb' : L x < ((n+2)%:R : R)%:E.
      apply: lt_le_trans hb _; by rewrite lee_fin ler_nat leq_addr.
    apply: hn; exists n=> //; by split=> //; split.
  have hadeq := @adequate_family_countable_almost_cover R X phi H Z A hh ha hnull.
  have [G hG] := hadeq setT openT.
  exists G; split; first exact: adequate_selection_members hG.
  split; first exact: adequate_selection_countable hG.
  split; first exact: adequate_selection_disjoint hG.
  by have := adequate_selection_remainder hG; rewrite setTI.
Qed.
