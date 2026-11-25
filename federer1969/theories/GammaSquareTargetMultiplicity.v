(** Federer (1969), 3.2.13, p. 250: the
    bounded square substitution has multiplicity two
    at positive target values up to the
    squared endpoint. The completed Gamma weight
    annihilates all nonpositive targets, including zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealMetricBackground EulerGammaMeasurable SquareIntervalFibre CountingPair
  CountingMeasure MappingMultiplicity MeasureBasic MeasureUP ScalarAbsoluteContinuousArea
  PartialFunctionUP PartialFunctionBasic SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [square_symmetric_interval_positive_multiplicity]: the
    actual counting multiplicity of the square
    map in the Gamma substitution, Federer
    3.2.13, p. 250, for positive targets. *)
Lemma square_symmetric_interval_positive_multiplicity (R:realType) (b y:R):
  (0<b)%R ->(0<y)%R ->
  @mapping_multiplicity R [the choiceType of real_line_metric R] R
    (fun x:R=>x^+2)%R `[(-b)%R,b] y=
    (if (y<=b^+2)%R then (2%R)%:E else 0).
Proof.
move=>hb hy; case:(leP y (b^+2)%R)=>hyb.
- have [q [hq [hQ hFibre]]]:=square_symmetric_interval_fibre_pair hb hy hyb.
  rewrite /mapping_multiplicity hFibre.
  have hDistinct:(q!= -q)%R.
    apply/eqP=>he; lra.
  exact:counting_measure_distinct_pair hDistinct.
- have hEmpty:=@square_symmetric_interval_fibre_empty R b y hb (or_intror hyb).
  rewrite /mapping_multiplicity hEmpty; exact:measure_empty (counting_measure_is_measure R _).
Qed.

(** Source for [gamma_square_target_cutoff]: completed target
    weight for a bounded symmetric square substitution,
    supporting Federer 3.2.13, p. 250. *)
Definition gamma_square_target_cutoff (R:realType) (s b y:R):R:=
  (if y<=b^+2 then 2*gamma_positive_completion s y else 0)%R.

(** Source for [gamma_square_area_target_graph]: the actual
    weighted counting integrand for the square
    map equals the bounded Gamma target weight,
    Federer 3.2.13, p. 250. The
    equality includes zero times infinity at nonpositive targets. *)
Lemma gamma_square_area_target_graph (R:realType) (s b:R):
  (0<b)%R ->forall y z,
  partial_function_graph (scalar_curve_area_target_integrand (fun x:R=>x^+2)%R `[(-b)%R,b]
    (gamma_positive_completion s)) y z <->
  partial_function_graph (real_total_integrand (gamma_square_target_cutoff s b)) y z.
Proof.
move=>hb y z; rewrite real_total_integrand_graph.
change ((gamma_positive_completion s y)%:E*
  @mapping_multiplicity R [the choiceType of real_line_metric R] R
    (fun x:R=>x^+2)%R `[(-b)%R,b] y=z <->(gamma_square_target_cutoff s b y)%:E=z).
case:(pselect ((0<y)%R))=>hy.
- rewrite (square_symmetric_interval_positive_multiplicity hb hy) /gamma_square_target_cutoff.
  case:ifP=>h.
  + by rewrite -EFinM (mulrC (gamma_positive_completion s y) (2%R:R)).
  + by rewrite mule0.
- have hZero:gamma_positive_completion s y= 0%R.
    rewrite /gamma_positive_completion; have hNot:(0<y)%R=false by apply/negP.
    by rewrite hNot.
  rewrite hZero mul0e /gamma_square_target_cutoff; case:ifP=>h; by rewrite ?hZero ?mulr0.
Qed.
