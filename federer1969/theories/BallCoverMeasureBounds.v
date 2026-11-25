(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover MeasureDisjointSupport
  NonnegativeSum NonnegativeSumScale MeasureDerivationContext DerivationOpenSupersets
  SmallCoefficientMeasureBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [disjoint_reference_cover_measure_bound]: supporting
    summation estimate in Federer 2.9.15, p. 161, first
    proof case. Covering sets H(j) need not be disjoint;
    disjoint measurable reference sets F(j) lie in E and
    control their numerator masses. Summation gives the printed
    coefficient times phi(E), also for infinite mass. *)
Lemma disjoint_reference_cover_measure_bound (R : realType) (X J : choiceType)
    (phi psi : set X -> \bar R) (T E : set X) (D : set J)
    (F H : J -> set X) (c : R) :
  is_measure phi -> is_measure psi -> (0<=c)%R -> countable D ->
  T `<=` \bigcup_(j in D) H j ->
  (forall j, D j -> F j `<=` E) ->
  (forall j, D j -> measure_measurable phi (F j)) ->
  (forall j k, D j -> D k -> j<>k -> F j `&` F k=set0) ->
  (forall j, D j -> psi (H j)<=c%:E*phi (F j)) -> psi T<=c%:E*phi E.
Proof.
move=> hphi hpsi hc hD hcover hFE hFm hdis hcell.
have hsum := @measure_indexed_cover R X J psi hpsi T D H hD hcover.
have hcmp : nonnegative_sum D (fun j => psi (H j))<=
    nonnegative_sum D (fun j => c%:E*phi (F j)).
  exact: nonnegative_sum_mono hcell.
have hscale := @nonnegative_sum_scale R J D (fun j => phi (F j)) c hc
  (fun j _ => measure_nonnegative hphi _).
have hbound := @measure_disjoint_sum_bound R X J phi hphi E D F hFE hFm hdis.
have hmul := @lee_wpmul2l R c%:E (ltac:(by rewrite lee_fin)) _ _ hbound.
rewrite hscale in hcmp; exact: le_trans hsum (le_trans hcmp hmul).
Qed.

(** Source for [null_measure_from_open_cover_bounds]: final
    passage in Federer 2.9.15, p. 161: the open set E
    containing the reference-null target can have arbitrarily
    small phi mass. A fixed finite nonnegative coefficient
    multiplying that mass therefore forces the numerator mass
    of the target to vanish. The numerator need not be in M
    for this supporting implication. *)
Lemma null_measure_from_open_cover_bounds (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (T : set X) (c : R) :
  is_derivation_measure phi -> is_measure psi -> (0<=c)%R -> phi T=0 ->
  (forall E, open E -> T `<=` E -> phi E< +oo -> psi T<=c%:E*phi E) -> psi T=0.
Proof.
move=> hphi hpsi hc hz hbound.
apply: (@finite_reference_small_coefficients_zero R (psi T) c%:E
  (measure_nonnegative hpsi T) (ltac:(by rewrite lee_fin)) (ltry c)).
move=> e he.
have [E [hE [hTE hmass]]] := @derivation_measure_open_superset R X phi T e hphi he.
rewrite hz add0e in hmass.
have hfin : phi E< +oo := le_lt_trans hmass (ltry e).
have hb := hbound E hE hTE hfin.
have hmul := @lee_wpmul2l R c%:E (ltac:(by rewrite lee_fin)) _ _ hmass.
apply: le_trans hb _.
rewrite [e%:E*c%:E]muleC; exact hmul.
Qed.
