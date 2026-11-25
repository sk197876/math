(** Federer (1969), 4.1.19, p. 377:
    bounded measurable form representatives have
    finite essential comass and may be
    chosen with that exact pointwise bound.
    The earlier essential-norm and null-modification
    laws retain zero measures and empty U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentCoefficientNorms PartialFunctionBasic
  MeasurableNormedFunctionUP MeasurableNormedBasic MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureEssentialNorm
  MeasureEssentialNormComparison MeasureEssentialNormAttainment
  EuclideanOpenDomainMeasure FlatCochainRepresentationUP.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section EssentialRepresentative.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n d : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation Y := (A_m X R^o d).
Local Notation N := (@current_form_comass R h2 n d).
Local Notation hN := (@current_form_comass_real_norm R h2 n d).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R n U hU)).
Local Notation ess phi := (measure_essential_norm mu N (partial_function_total phi)).

(** Source for [bounded_current_form_essential_bound]:
    a pointwise comass bound gives the
    same essential bound, supporting the norm
    display of Federer 4.1.19, p. 377.
    This direction does not identify global
    pointwise comass with essential comass. *)
Theorem bounded_current_form_essential_bound (phi : UT -> Y) (c : R) :
  0 <= c -> (forall x, N (phi x) <= c) -> (ess phi <= c%:E)%E.
Proof.
move=> hC hCap.
apply: (@measure_essential_norm_of_almost_bound R UT Y mu hMu N
  (partial_function_total phi) c%:E); first by rewrite lee_fin.
apply: (@measure_almost_everywhere_mono R UT mu hMu setT _ _
  (measure_almost_everywhere_true hMu))=> x _.
exists (phi x); split; first exact: erefl.
by rewrite lee_fin; exact: hCap.
Qed.

(** Source for [bounded_current_form_essential_value]:
    bounded measurable forms have a finite
    nonnegative essential comass, supporting the
    original representation in Federer 4.1.19,
    p. 377. The bound is attained
    almost everywhere in the preceding essential-norm sense. *)
Theorem bounded_current_form_essential_value (phi : UT -> Y) :
  @is_bounded_measurable_current_form R h2 n U d phi ->
  exists a : R, 0 <= a /\ ess phi=a%:E /\
    measure_almost_everywhere mu [set x | N (phi x) <= a].
Proof.
move=> [hPhi [c [hC hCap]]].
have hUpper := bounded_current_form_essential_bound hC hCap.
have hNonnegative := measure_essential_norm_nonnegative mu N (partial_function_total phi).
have hFinite : ess phi \is a fin_num.
  rewrite ge0_fin_numE; first exact: (le_lt_trans hUpper (ltry c)).
  exact: hNonnegative.
pose a := fine (ess phi).
have hExact : ess phi=a%:E by rewrite /a fineK.
have hAlmost := @measure_essential_norm_almost_bound R UT Y mu hMu N
  (partial_function_total phi).
have hDomain : measure_almost_everywhere mu
    (partial_function_domain (partial_function_total phi)).
  rewrite partial_function_total_domain.
  exact: (@measure_almost_everywhere_true R UT mu hMu).
have hBound := hAlmost hDomain.
exists a; split.
- by rewrite -lee_fin -hExact.
split; first exact: hExact.
apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hBound).
move=> x [y [hY hValue]].
have hSame : phi x=y := hY.
by rewrite -hSame hExact lee_fin in hValue.
Qed.

(** Source for [bounded_current_form_essential_representative]:
    choose a bounded representative with its
    exact essential bound without changing its
    almost class, supporting Federer 4.1.19,
    p. 377. The clipping follows the
    earlier density representative selection in 2.5.7,
    rather than a change to global comass. *)
Theorem bounded_current_form_essential_representative (phi : UT -> Y) :
  @is_bounded_measurable_current_form R h2 n U d phi ->
  exists a : R, exists psi : UT -> Y,
    0 <= a /\ ess phi=a%:E /\
    @is_bounded_measurable_current_form R h2 n U d psi /\
    (forall x, N (psi x) <= a) /\
    measure_almost_everywhere mu [set x | phi x=psi x].
Proof.
move=> hPhi.
have [a [hA [hExact hAlmost]]] := bounded_current_form_essential_value hPhi.
pose psi (x : UT) : Y := if pselect (N (phi x) <= a) then phi x else 0.
have hPoint (x : UT) (hx : N (phi x) <= a) : psi x=phi x.
  by rewrite /psi; case: pselect.
have hEqual : measure_almost_everywhere mu [set x | phi x=psi x].
  apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hAlmost)=> x hx.
  exact: esym (@hPoint x hx).
have hPartial : measure_almost_equal mu
    (partial_function_total (fun x => (phi x : real_norm_metric_space hN)))
    (partial_function_total (fun x => (psi x : real_norm_metric_space hN))).
  apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hEqual)=> x hx.
  exists (phi x); split; first exact: erefl.
  exact: esym hx.
have hPsiMeas := @measurable_normed_almost_equal R UT Y N hN mu hMu _ _
  hPhi.1 hPartial.
have hCap (x : UT) : N (psi x) <= a.
  rewrite /psi; case: pselect=> [hx|hx]; first exact: hx.
  by rewrite (real_seminorm_zero hN.1).
exists a,psi; split; first exact: hA.
split; first exact: hExact.
split.
- split; first exact: hPsiMeas.
  exists a; by split.
split; first exact: hCap.
exact: hEqual.
Qed.
End EssentialRepresentative.
