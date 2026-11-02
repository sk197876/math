(** Federer (1969), 2.5.17, p. 111: the measures psi^+ and psi^- induced by
    g are Borel regular, and the one dimensional Lebesgue measure L^1 is a
    Borel regular measure with L^1{x : a <= x <= b} = b - a. The real line
    has a countable base of open intervals with rational end points; by
    2.5.14 a K(R) regular measure representing a functional on K(R) is then
    a Radon measure, and Radon measures are Borel regular by 2.2.5. A
    measure representing a functional on K(R)+ also represents the
    functional f -> lambda(f^+) - lambda(f^-) on K(R). The characterisation
    of L^1 among Borel regular measures is not formalised here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground ExtendedRealBoundsUP ExtendedRealBounds
  CountableOpenBaseUP RadonMeasureUP BorelRegularMeasureUP RadonBorelRegularity
  CompactSupportCountableRadon CurveVariationUP CurveArcLength FunctionLatticeUP
  FunctionLatticeLaws FunctionLatticeRegularityUP PositiveLatticeRegularity DaniellIntegralUP
  MonotoneDaniellIntegralUP DaniellVariationUP DaniellVariationBounds DaniellVariationFunctionals
  DaniellRepresentation DaniellCoverUP RegularDaniellEnvelope RealIntegralFunctionalUP MeasureUP
  MeasureBasic MeasureIntegralUP SummableRealFunctionUP SummableRealArithmetic
  CompactSupportFunctionUP CompactSupportFunctionLattice StieltjesSums StieltjesIntegral
  StieltjesDaniellIntegral IntervalBumpFunctions StieltjesInducedMeasures StieltjesMonotone
  LebesgueLineMeasure StieltjesContinuityPoints StieltjesContinuousIntegrator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section BorelRegularity.
Variable R : realType.
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation KRp := (positive_function_lattice KR).

(** Source for [real_line_countable_open_base_exists]: the open
    intervals with rational end points form a countable base of the real
    line, the countability hypothesis of 2.5.14, p. 107, used in Federer
    2.5.17, p. 111. *)
Lemma real_line_countable_open_base_exists : exists U : nat -> set R, is_countable_open_base U.
Proof.
exists (fun n => if n is k.+1 then
  (if @unpickle (rat * rat)%type k is Some pq then `](ratr pq.1 : R), ratr pq.2[ else set0)
  else set0).
constructor.
- move=> [|k]; first exact: open0.
  case: (@unpickle (rat * rat)%type k)=> [[p q]|]; last exact: open0.
  have h : open (`](ratr p : R), ratr q[ : set R^o) by apply: interval_open.
  exact: h.
- by [].
- move=> V hV x hVx.
  have hn : nbhs x V by apply: open_nbhs_nbhs; split.
  have [e he hball] := (nbhs_ballP x V).1 hn.
  have he' : 0 < e := he.
  have hlt1 : x - e < x by lra.
  have hlt2 : x < x + e by lra.
  have [p hp] := rat_in_itvoo hlt1.
  have [q hq] := rat_in_itvoo hlt2.
  move: hp hq; rewrite !in_itv /= => /andP[hp1 hp2] /andP[hq1 hq2].
  exists (pickle (p, q)).+1; rewrite pickleK /=; split.
    by rewrite in_itv /= hp2 hq1.
  move=> y; rewrite /= in_itv /= => /andP[hy1 hy2]; apply: hball.
  by rewrite /ball /= ltr_norml; apply/andP; split; lra.
Qed.

(** Source for [positive_representation_signed]: a measure representing
    a functional P on K(R)+ represents f -> P(f^+) - P(f^-) on K(R),
    Federer 2.5.1, p. 92, and 2.4.4, p. 82, used in 2.5.17, p. 111. *)
Lemma positive_representation_signed (mu : set R -> \bar R) (P : (R -> R) -> R) :
  is_measure mu -> is_real_integral_functional mu KRp P ->
  is_real_integral_functional mu KR
    (fun f => P (fun x => Order.max (f x) 0) - P (fun x => Order.max (- f x) 0)).
Proof.
move=> hm hi f hf.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hp : KRp (fun x => Order.max (f x) 0).
  by split; [exact (function_lattice_positive_part hL hf) | move=> x; rewrite le_max lexx orbT].
have hn : KRp (fun x => Order.max (- f x) 0).
  by split; [exact (function_lattice_negative_part hL hf) | move=> x; rewrite le_max lexx orbT].
have := real_total_integral_subtract hm (hi _ hp) (hi _ hn).
suff -> : (fun x => Order.max (f x) 0 - Order.max (- f x) 0) = f by [].
apply/funext=> x /=; case: (leP 0 (f x))=> h.
- by rewrite max_r ?subr0 // oppr_le0.
- by rewrite max_l ?sub0r ?opprK // oppr_ge0 ltW.
Qed.

(** Source for [real_line_regular_radon]: a K(R) regular measure
    representing a functional on K(R) is a Radon measure and Borel
    regular, Federer 2.5.14, p. 107, and 2.2.5, p. 62, used in 2.5.17,
    p. 111. *)
Theorem real_line_regular_radon (mu : set R -> \bar R) (A : (R -> R) -> R) :
  is_measure mu -> is_real_integral_functional mu KR A -> is_function_lattice_regular KR mu ->
  is_radon_measure mu /\ is_borel_regular_measure mu.
Proof.
move=> hm hA hr.
have [B hB] := real_line_countable_open_base_exists.
have hrad := @compact_support_regular_countable_base_radon R R mu A hm hA hr B
  (@Rhausdorff R) (@locally_compactR R) hB.
by split=> //; exact: radon_borel_regular hm hrad.
Qed.

(** Source for [positive_regular_radon]: a K(R)+ regular measure
    representing a functional on K(R)+ is a Radon measure and Borel
    regular, Federer 2.5.14, p. 107, used in 2.5.17, p. 111. *)
Theorem positive_regular_radon (mu : set R -> \bar R) (P : (R -> R) -> R) :
  is_measure mu -> is_real_integral_functional mu KRp P -> is_function_lattice_regular KRp mu ->
  is_radon_measure mu /\ is_borel_regular_measure mu.
Proof.
move=> hm hi hr.
exact: real_line_regular_radon hm (positive_representation_signed hm hi)
  ((@function_lattice_regular_positive_iff R R KR mu).1 hr).
Qed.

(** Source for [lebesgue_line_measure_borel_regular]: the one
    dimensional Lebesgue measure L^1 is a Radon measure and Borel regular,
    with L^1{x : a <= x <= b} = b - a, Federer 2.5.17, p. 111. *)
Theorem lebesgue_line_measure_borel_regular :
  exists L1 : set R -> \bar R, is_measure L1 /\ is_radon_measure L1 /\ is_borel_regular_measure L1 /\
    is_function_lattice_regular KR L1 /\
    is_real_integral_functional L1 KR (induced_daniell (fun x : R => x)) /\
    (forall a b : R, a <= b -> L1 `]a, b[ = (b - a)%:E) /\
    (forall a b : R, a <= b -> L1 `[a, b] = (b - a)%:E).
Proof.
have [L1 [hm [hr [hi [ho hc]]]]] := @lebesgue_line_measure_exists R.
have [hrad hbor] := real_line_regular_radon hm hi hr.
by exists L1.
Qed.

Variable g : R -> R.
Hypothesis hg : curve_locally_finite_variation (g : R -> real_line_metric R).

(** Source for [stieltjes_borel_regular_induced_measures]: the measures
    psi^+ and psi^- induced by g are Radon measures and Borel regular and
    satisfy the conditions (1) and (2) of Federer 2.5.17, p. 111, with
    the consequences at points of continuity of g and the equality in (2)
    for continuous g. *)
Theorem stieltjes_borel_regular_induced_measures :
  exists (P Q : (R -> R) -> R) (psip psim : set R -> \bar R),
    is_daniell_positive_variation KR (induced_daniell g) P /\
    is_daniell_negative_variation KR (induced_daniell g) Q /\
    is_measure psip /\ is_measure psim /\
    is_radon_measure psip /\ is_radon_measure psim /\
    is_borel_regular_measure psip /\ is_borel_regular_measure psim /\
    is_function_lattice_regular KR psip /\ is_function_lattice_regular KR psim /\
    (forall f, KR f -> exists u v : R,
      is_measure_integral psip (real_total_integrand f) u%:E /\
      is_measure_integral psim (real_total_integrand f) v%:E /\ induced_daniell g f = u - v) /\
    (forall a b : R, a <= b -> (psip `]a, b[ + psim `]a, b[ <= (total_variation g a b)%:E)%E) /\
    (forall x : R, g @ x --> g x -> psip [set x] = 0%E /\ psim [set x] = 0%E) /\
    (forall a b : R, a < b -> g @ a --> g a -> g @ b --> g b ->
      (g b - g a)%:E = (psip `]a, b[ - psim `]a, b[)%E /\
      (g b - g a)%:E = (psip `[a, b] - psim `[a, b])%E) /\
    (continuous g -> forall a b : R, a <= b ->
      (psip `]a, b[ + psim `]a, b[)%E = (total_variation g a b)%:E).
Proof.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hD := induced_daniell_is_daniell hg.
have hne : exists f, KR f by exists (fun _ => 0); exact: compactly_supported_zero_function.
have [P [Q [psip [psim [hP [hQ [hm [hn [hr [hs [hi [hj [hform _]]]]]]]]]]]]] :=
  daniell_integral_representation hL hD hne.
have hLp : is_function_lattice KRp := positive_lattice_is_lattice hL.
have henvP := regular_representing_measure_envelope hLp hm hi hr.
have henvQ := regular_representing_measure_envelope hLp hn hj hs.
have hbound := induced_cost_bound hg hP hQ henvP henvQ.
have hbp : forall t u, t <= u -> (psip `]t, u[ <= (total_variation g t u)%:E)%E.
  move=> t u htu; apply: le_trans _ (hbound t u htu).
  exact: lee_paddr (measure_nonnegative hn _) (lexx _).
have hbm : forall t u, t <= u -> (psim `]t, u[ <= (total_variation g t u)%:E)%E.
  move=> t u htu; apply: le_trans _ (hbound t u htu).
  exact: lee_paddl (measure_nonnegative hm _) (lexx _).
have hpoint : forall x : R, g @ x --> g x -> psip [set x] = 0%E /\ psim [set x] = 0%E.
  by move=> x hc; split; [exact (induced_point_mass_zero hg hm hbp hc) |
    exact (induced_point_mass_zero hg hn hbm hc)].
have hincr : forall a b : R, a < b -> g @ a --> g a -> g @ b --> g b ->
    (g b - g a)%:E = (psip `]a, b[ - psim `]a, b[)%E /\
    (g b - g a)%:E = (psip `[a, b] - psim `[a, b])%E.
  move=> a b hab hca hcb.
  have hopen := induced_increment_open hg hP hQ henvP henvQ hm hn hbound hab hca hcb.
  split=> //.
  have [h0a h0a'] := hpoint a hca.
  have [h0b h0b'] := hpoint b hcb.
  by rewrite (measure_segment_open_interval hm h0a h0b) (measure_segment_open_interval hn h0a' h0b').
have [hradp hborp] := positive_regular_radon hm hi hr.
have [hradm hborm] := positive_regular_radon hn hj hs.
exists P, Q, psip, psim; do 8!(split=> //).
split; first exact ((@function_lattice_regular_positive_iff R R KR psip).1 hr).
split; first exact ((@function_lattice_regular_positive_iff R R KR psim).1 hs).
split=> //; split=> //; split=> //; split=> //.
move=> hc a b hab; apply/le_anti; rewrite hbound //=.
apply: (continuous_variation_le_induced hg hm hn hi hj hbound _ hab)=> t u htu.
exact: (hincr t u htu (hc t) (hc u)).1.
Qed.

End BorelRegularity.
