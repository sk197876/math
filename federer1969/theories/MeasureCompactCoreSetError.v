(** Federer (1969), 4.1.23, p. 379:
    finite measurable sets can be replaced by
    disjoint box unions near a compact core.
    The earlier box-covering law gives a lower
    volume bound, which suffices for both errors
    and the separate mass budget. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal lra.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure
  MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_compact_core_set_error]: the
    measurable-cell approximation in Federer 4.1.23,
    p. 379, by the earlier compact
    core and open-box covering laws. The lower
    volume bound mu(F)<=mu(G) replaces any
    unstated claim that F minus G is
    null. The two actual error measures and
    the separate mass allowance are both controlled. *)
Theorem measure_compact_core_set_error (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (A F G : set X) (eta : R) :
  measure_measurable mu A -> measure_measurable mu F -> measure_measurable mu G ->
  (mu A< +oo)%E -> F `<=` A -> 0<eta ->
  (mu (A `\` F)<eta%:E)%E -> (mu (G `\` F)<eta%:E)%E ->
  (mu F<=mu G)%E ->
  (mu G< +oo)%E /\
  (mu (A `\` G)+mu (G `\` A)<(3*eta)%:E)%E /\
  (mu G<mu A+eta%:E)%E.
Proof.
move=> hA hF hG hAFinite hFA hEta hAError hGError hLower.
have hFFinite : (mu F< +oo)%E := le_lt_trans (measure_mono hm hFA) hAFinite.
have hGErrorFinite : (mu (G `\` F)< +oo)%E := lt_trans hGError (ltry eta).
have hCover : G `<=` F `|` (G `\` F).
  move=> x hx; case: (pselect (F x))=> hFx; [by left|right; by split].
have hGUpper := @measure_binary_cover R X mu hm G F (G `\` F) hCover.
have hGFinite : (mu G< +oo)%E := le_lt_trans hGUpper
  (lte_add_pinfty hFFinite hGErrorFinite).
have hAValue : mu A \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hm A)).
have hFValue : mu F \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hm F)).
have hGValue : mu G \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hm G)).
have hGFValue : mu (G `\` F) \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hm (G `\` F))).
have hAFValue : mu (A `\` F) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm (A `\` F))).
  exact: lt_trans hAError (ltry eta).
have hGA : (G `\` A) `<=` (G `\` F).
  move=> x [hx hNotA]; split; first exact: hx.
  move=> hFx; exact: hNotA (@hFA x hFx).
have hGAError := le_lt_trans (measure_mono hm hGA) hGError.
have hGAValue : mu (G `\` A) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm (G `\` A))).
  exact: lt_trans hGAError (ltry eta).
have hAGValue : mu (A `\` G) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm (A `\` G))).
  apply: (le_lt_trans _ hAFinite).
  apply: (@measure_mono R X mu hm (A `\` G) A)=> x hx; exact: hx.1.
have hIntersectionValue : mu (A `&` G) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm (A `&` G))).
  apply: (le_lt_trans _ hAFinite).
  apply: (@measure_mono R X mu hm (A `&` G) A)=> x hx; exact: hx.1.
pose a := fine (mu A).
pose b := fine (mu G).
pose c := fine (mu F).
pose d := fine (mu (A `\` F)).
pose e := fine (mu (G `\` A)).
pose f := fine (mu (A `\` G)).
pose t := fine (mu (A `&` G)).
have hAFSet : A `&` F=F.
  apply/seteqP; split; first by move=> x hx; exact: hx.2.
  move=> x hx; split; [exact: @hFA x hx|exact: hx].
have hAEquation : a=c+d.
  have h := hF A; rewrite hAFSet -(fineK hAValue) -(fineK hFValue)
    -(fineK hAFValue) -EFinD in h.
  exact: EFin_inj h.
have hAGEquation : a=t+f.
  have h := hG A; rewrite -(fineK hAValue) -(fineK hIntersectionValue)
    -(fineK hAGValue) -EFinD in h.
  exact: EFin_inj h.
have hGAEquation : b=t+e.
  have h := hA G; rewrite setIC -(fineK hGValue) -(fineK hIntersectionValue)
    -(fineK hGAValue) -EFinD in h.
  exact: EFin_inj h.
have hLowerR : c<=b by move: hLower; rewrite -(fineK hFValue) -(fineK hGValue) lee_fin.
have hDError : d<eta by move: hAError; rewrite -(fineK hAFValue) lte_fin.
have hEError : e<eta by move: hGAError; rewrite -(fineK hGAValue) lte_fin.
have hError : f+e<3*eta by rewrite /a /b /c /d /e /f /t in hAEquation hAGEquation hGAEquation hLowerR hDError hEError |- *; lra.
have hMass : (mu G<mu A+eta%:E)%E.
  have hFirst : (mu F<=mu A)%E := measure_mono hm hFA.
  have hFirstR : c<=a by move: hFirst; rewrite -(fineK hFValue) -(fineK hAValue) lee_fin.
  have hUpperR : b<=c+fine (mu (G `\` F)).
    by move: hGUpper; rewrite -(fineK hGValue) -(fineK hFValue)
      -(fineK hGFValue) -EFinD lee_fin.
  have hErrorR : fine (mu (G `\` F))<eta.
    by move: hGError; rewrite -(fineK hGFValue) lte_fin.
  rewrite -(fineK hGValue) -(fineK hAValue) -EFinD lte_fin.
  change (is_true (b<a+eta)); lra.
split; first exact: hGFinite.
split; last exact: hMass.
rewrite -(fineK hAGValue) -(fineK hGAValue) -EFinD lte_fin.
exact: hError.
Qed.
