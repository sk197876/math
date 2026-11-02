(** Federer (1969), 2.2.2(2), p. 61: open outer approximation of a Borel set
    covered by countably many open sets of finite measure. Closed inner
    approximants to V_i minus B give the desired open union. Source context
    and geometric-error convention: GeometricErrorBudget.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology pseudometric_structure.
From Federer Require Import MeasureUP MeasureBasic TopologicalBorel ClosedApproximationUP
  BorelClosedApproximation OpenCoverApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_borel_open_approximation]: Federer
    2.2.2(2), p. 61, direct formalisation. The Borel set B
    may have infinite measure; it is covered by a sequence of open
    finite-measure sets. For every positive epsilon there is an
    open superset W with mu(W minus B) below epsilon. *)
Theorem metric_borel_open_approximation (R : realType) (T : pseudoMetricType R)
    (mu : set T -> \bar R) (hm : is_measure mu) (B : set T)
    (V : nat -> set T) (epsilon : R) :
  (forall U, open U -> measure_measurable mu U) -> borel_set B ->
  (forall n, open (V n) /\ mu (V n) < +oo) ->
  B `<=` \bigcup_n V n -> (0 < epsilon)%R ->
  exists W, open W /\ B `<=` W /\ mu (W `\` B) < epsilon%:E.
Proof.
move=> ho hB hV hcover he.
have hD n : is_closed_approximable mu (V n `\` B).
  apply: (@metric_borel_closed_approximation R T mu hm (V n `\` B) ho).
  - exact: borel_set_difference (open_borel_set (hV n).1) hB.
  - apply: le_lt_trans _ (hV n).2.
    apply: (@measure_mono R _ mu hm _ (V n))=> x [hx _]; exact hx.
exact: (@open_cover_from_closed_complements R T mu hm B V epsilon
  (fun n => (hV n).1) hcover hD he).
Qed.
