(** Federer (1969), 2.2.3, pp. 61-62: for a Borel regular measure the two
    metric approximation results of 2.2.2 extend to every measurable set.
    Source context: BorelRegularMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology pseudometric_structure.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure
  BorelRegularMeasureUP BorelRegularSandwich ClosedApproximationUP
  BorelClosedApproximation OpenCoverApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_regular_closed_approximation]: Federer 2.2.3, pp.
    61-62, extension of 2.2.2(1) to a measurable finite-measure set A. Apply
    the Borel case to the inner Borel set D furnished by the null-difference
    construction on p. 61. *)
Theorem borel_regular_closed_approximation (R : realType) (T : pseudoMetricType R)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) A :
  measure_measurable mu A -> mu A < +oo -> is_closed_approximable mu A.
Proof.
move=> hA hf; have [D [B [hD [hB [hDA [hAB hnull]]]]]] :=
  @borel_regular_finite_sandwich R T mu hm hr A hA hf.
have hDf : mu D < +oo := le_lt_trans (@measure_mono R _ mu hm D A hDA) hf.
have happ := @metric_borel_closed_approximation R T mu hm D
  (borel_regular_open_measurable hr) hD hDf.
move=> epsilon he; have [C [hC [hCD herror]]] := happ epsilon he.
exists C; split=> //; split; first by move=> x hx; exact: hDA (hCD x hx).
have hcover : A `\` C `<=` (B `\` D) `|` (D `\` C).
  move=> x [ha hn]; case: (pselect (D x))=> hd.
  - right; by split.
  - left; split=> //; exact: hAB.
have hb := @measure_binary_cover R _ mu hm (A `\` C) (B `\` D) (D `\` C) hcover.
rewrite hnull add0e in hb; exact: le_lt_trans hb herror.
Qed.

(** Source for [borel_regular_open_approximation]: Federer 2.2.3, p. 62,
    extension of 2.2.2(2) to a measurable set B covered by countably many
    open sets of finite measure. Retains the finite-open-cover hypothesis,
    without assuming mu(B) finite. *)
Theorem borel_regular_open_approximation (R : realType) (T : pseudoMetricType R)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) B (V : nat -> set T) epsilon :
  measure_measurable mu B -> (forall n, open (V n) /\ mu (V n) < +oo) ->
  B `<=` \bigcup_n V n -> (0 < epsilon)%R ->
  exists W, open W /\ B `<=` W /\ mu (W `\` B) < epsilon%:E.
Proof.
move=> hB hV hcover he.
apply: (@open_cover_from_closed_complements R T mu hm B V epsilon
  (fun n => (hV n).1) hcover _ he)=> n.
apply: (@borel_regular_closed_approximation R T mu hm hr (V n `\` B)).
- apply: (@measure_measurable_difference R _ mu hm (V n) B _ hB).
  exact: (@borel_regular_open_measurable R T mu hr (V n) (hV n).1).
- apply: le_lt_trans (_ : mu (V n `\` B) <= mu (V n)) (hV n).2.
  apply: (@measure_mono R _ mu hm)=> x [hx _]; exact hx.
Qed.
