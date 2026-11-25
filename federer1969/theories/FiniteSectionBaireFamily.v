(** Supporting Federer (1969), 2.10.46, p. 204: for a finite first-factor
    measure, the sets with measurable horizontal sections and a Baire real
    section-volume function form a Dynkin family. Nested differences use
    finite measure subtraction; disjoint unions use increasing continuity
    and the Baire pointwise-limit law of 2.2.15, pp. 70–71. This supplies a
    proved Borel-generation step rather than an assumed parameter-integral
    measurability law. Source context: FiniteMeasureRealLaws.v and
    BaireFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground DynkinFamilyUP ProductSections MeasureUP MeasureBasic MeasureSplit
  MeasureFiniteClosure MeasureCountableClosure MeasureSequencePrefixes SetSequenceDisjointification
  FiniteMeasureRealLaws BaireFunctions BaireRealAlgebra PointwiseLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_horizontal_sections_baire_dynkin]:
    supporting section-family closure for 2.10.46, p. 204,
    using the measure laws of 2.1.3, pp. 54–55,
    and the abstract Baire class of 2.2.15, pp. 70–71. *)
Theorem finite_horizontal_sections_baire_dynkin (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu) :
  mu setT< +oo -> is_dynkin_family
    [set S : set (X*Y) | (forall y, measure_measurable mu (product_horizontal_section S y)) /\
      @is_baire_function R Y [the metricType R of real_line_metric R]
        (fun y=>fine (mu (product_horizontal_section S y)))].
Proof.
move=> hfinite; constructor.
- split; first by move=> y; exact: measure_measurable_whole hm.
  exact (@baire_real_constant R Y (fine (mu setT))).
- move=> A B [hAm hAb] [hBm hBb] hAB; split.
  + move=> y; change (measure_measurable mu (product_horizontal_section B y `\` product_horizontal_section A y)).
    exact: (@measure_measurable_difference R X mu hm _ _ (hBm y) (hAm y)).
  + have he : (fun y=>fine (mu (product_horizontal_section (B `\` A) y)))=
        (fun y=>(fine (mu (product_horizontal_section B y))-fine (mu (product_horizontal_section A y)))%R).
      apply: funext=> y.
      apply: (@finite_total_measure_difference_fine R X mu hm _ _ hfinite (hAm y))=> x hx.
      exact: hAB (x,y) hx.
    rewrite he; exact: baire_real_add hBb (baire_real_opp hAb).
- move=> A hA hd.
  pose T n y := product_horizontal_section (A n) y.
  have hT n y : measure_measurable mu (T n y) := (hA n).1 y.
  have hdis n m : n != m -> forall y x, T n y x -> T m y x -> False.
    move=> hne y x hn hm'; exact: hd n m hne (x,y) hn hm'.
  have hp n : @is_baire_function R Y [the metricType R of real_line_metric R]
      (fun y=>fine (mu (set_sequence_prefix (fun j=>T j y) n))).
    elim: n=> [|n ih].
    + have he : (fun y=>fine (mu (set_sequence_prefix (fun j=>T j y) 0)))=(fun _ : Y=>0%R).
        by apply: funext=> y; rewrite set_sequence_prefix_zero (measure_empty hm).
      rewrite he; exact: baire_real_constant.
    + have he : (fun y=>fine (mu (set_sequence_prefix (fun j=>T j y) n.+1)))=
          (fun y=>(fine (mu (set_sequence_prefix (fun j=>T j y) n))+fine (mu (T n y)))%R).
        apply: funext=> y; rewrite set_sequence_prefix_succ.
        apply: (@finite_total_measure_disjoint_union_fine R X mu hm _ _ hfinite).
        * exact (@measure_sequence_prefix_measurable R X mu hm (fun j=>T j y) (fun j=>hT j y) n).
        * move=> x [j hj hx] hn; apply: (hdis j n _ y x hx hn).
          by rewrite neq_ltn hj.
      rewrite he; exact: baire_real_add ih (hA n).2.
  split.
  + move=> y; change (measure_measurable mu (\bigcup_n T n y)).
    exact (@measure_measurable_sequence_union R X mu hm (fun n=>T n y) (fun n=>hT n y)).
  + apply: (@baire_function_pointwise_limit R Y [the metricType R of real_line_metric R]
      (fun n y=>fine (mu (set_sequence_prefix (fun j=>T j y) n))) _ hp).
    move=> y.
    have hlim := @finite_total_measure_increasing_real_limit R X mu hm
      (fun n=>set_sequence_prefix (fun j=>T j y) n) hfinite
      (@measure_sequence_prefix_measurable R X mu hm (fun j=>T j y) (fun j=>hT j y))
      (@set_sequence_prefix_mono X (fun j=>T j y)).
    have he : (\bigcup_n set_sequence_prefix (fun j=>T j y) n)=product_horizontal_section (\bigcup_n A n) y.
      apply/seteqP; split=> [x [n _ [j hj hx]]|x [j _ hx]].
      * by exists j.
      * exists j.+1=> //; exists j=> //; exact: ltnSn.
    by rewrite he in hlim.
Qed.
