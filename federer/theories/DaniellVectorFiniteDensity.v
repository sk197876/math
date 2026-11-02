(** Federer (1969), 2.5.12, printed p. 105: replace characteristic functions
    t_i by positive lattice functions h_i, then form eta = sum h_i y_i. The
    scalar approximation is 2.5.3, p. 94, proved on p. 95. It has no
    corresponding vector representation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureBasic MeasureAlmostUP MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasureIntegralUniqueness
  FunctionLatticeUP FunctionLatticeLaws FunctionLatticeRegularityUP
  RealIntegralFunctionalUP SummableRealFunctionUP SummableRealArithmetic
  RegularDaniellEnvelope DaniellPositiveL1Density TotalAbsoluteDifferenceGraph
  RealTotalCharacteristicBounds CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureCharacteristicIntegral CharacteristicVectorPiece MeasurableNormedBasic
  MeasurableNormedFunctionUP MeasurableTotalNormedArithmetic
  MeasurableFunctionBorel TopologicalBorel
  MeasureLpMembershipUP MeasureLpFiniteFibres FiniteDeltaVectorSum
  VectorLoneApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Density.
Variable R : realType.
Variable X : choiceType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Variable L : set (X -> R).
Variable F : (X -> R) -> R.
Hypothesis hL : is_function_lattice L.
Hypothesis hF : is_real_integral_functional phi (positive_function_lattice L) F.
Hypothesis hreg : is_function_lattice_regular (positive_function_lattice L) phi.
Variable D : set E.
Variable G : set (X -> E).
Hypothesis hG0 : G (fun _ => 0).
Hypothesis hGadd : forall u v, G u -> G v -> G (fun x => u x+v x).
Hypothesis hGA : forall u, G u -> is_measurable_normed_function phi
  (partial_function_total (u : X -> real_norm_metric_space hN)).
Hypothesis hGelem : forall f y, positive_function_lattice L f -> D y ->
  G (fun x => f x *: y).

(** Source for [daniell_vector_characteristic_approximation]:
    the replacement t_i y_i by h_i y_i in Federer
    2.5.12, p. 105. A zero vector is handled separately,
    without assuming that its fibre has finite measure. *)
Lemma daniell_vector_characteristic_approximation (S : set X)
    (s : X -> R) (y : E) :
  is_characteristic_function S s -> measure_measurable phi S ->
  (y != 0 -> (phi S < +oo)%E) -> D y ->
  is_vector_lone_approximable N phi G (fun x => s x *: y).
Proof.
move=> hs hS hfin hy.
case: (eqVneq y 0)=> [->|hy0].
  have he : (fun x => s x *: (0 : E))=(fun _ : X => 0).
    by apply: funext=> x; rewrite scaler0.
  rewrite he; exact (@vector_lone_approximable_member R X E N hN phi hphi G _ hG0).
move=> e he.
have hny : 0 < N y by rewrite (real_norm_positive hN.1 hN.2).
have hdelta : 0 < e/N y by rewrite divr_gt0.
have hs0 : function_nonnegative s.
  move=> x; case: (pselect (S x))=> hx.
  - by rewrite (characteristic_on_set hs hx).
  - by rewrite (characteristic_off_set hs hx).
have hsf : phi S \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hphi S)); exact: hfin.
have hi : is_measure_integral phi (real_total_integrand s) (fine (phi S))%:E.
  rewrite fineK //; exact (@measure_characteristic_integral R X phi hphi S s hs hS).
have hsum : is_measure_summable phi (real_total_integrand s) by exists (fine (phi S)).
have hc := @regular_representing_measure_envelope R X (positive_function_lattice L)
  F (positive_function_lattice_laws hL) phi hphi hF hreg.
have [h [q [hh [hqi hqe]]]] := @daniell_nonnegative_summable_lattice_density
  R X (positive_function_lattice L) F (positive_function_lattice_laws hL)
  phi hphi hF hc (real_total_integrand s) (e/N y) hsum
  (real_total_nonnegative_almost hphi hs0) hdelta.
have hqi' : is_measure_integral phi (real_total_integrand (fun x => `|h x-s x|)) q%:E.
  exact (@measure_integral_graph_equivalent R X phi _ _ _ (total_absolute_difference_graph h s) hqi).
exists (fun x => h x *: y),(N y*q); split; first exact (@hGelem h y hh.1 hy).
split.
- have hn : (fun x => N (s x *: y-h x *: y))=
      (fun x => N y*`|h x-s x|).
    apply: funext=> x; rewrite -scalerBl (real_seminorm_scale hN.1).
    by rewrite distrC mulrC.
  rewrite hn; exact (@real_total_integral_scale R X phi hphi _ q (N y) hqi').
- have heq : N y*(e/N y)=e by rewrite mulrC -mulrA mulVf ?mulr1 //; exact: lt0r_neq0 hny.
  rewrite -heq; by rewrite ltr_pM2l.
Qed.

(** Source for [daniell_vector_finite_sum_approximation]: the
    finite-sum triangle estimate in Federer 2.5.12, p. 105.
    Each characteristic piece is required to be measurable;
    the vectors and scalar approximations remain abstract. *)
Lemma daniell_vector_finite_sum_approximation (J : eqType) (s : seq J)
    (u : J -> X -> real_norm_metric_space hN) :
  (forall j, j \in s -> is_measurable_normed_function phi (partial_function_total (u j))) ->
  (forall j, j \in s -> is_vector_lone_approximable N phi G (u j)) ->
  is_measurable_normed_function phi (partial_function_total (fun x => \sum_(j <- s) u j x)) /\
  is_vector_lone_approximable N phi G (fun x => \sum_(j <- s) u j x).
Proof.
elim: s=> [|j s ih] hA ha.
- have he : (fun x : X => \sum_(j <- [::]) u j x)=(fun _ : X => 0).
    by apply: funext=> x; rewrite big_nil.
  rewrite he; split.
  + exact: hGA hG0.
  + exact (@vector_lone_approximable_member R X E N hN phi hphi G _ hG0).
- have hj : j \in j::s by rewrite in_cons eqxx.
  have hsub i : i \in s -> i \in j::s by move=> hi; rewrite in_cons hi orbT.
  have [hAs has] := ih (fun i hi => hA i (hsub i hi)) (fun i hi => ha i (hsub i hi)).
  have he : (fun x => \sum_(i <- j::s) u i x)=(fun x => u j x+\sum_(i <- s) u i x).
    by apply: funext=> x; rewrite big_cons.
  rewrite he; split.
  + exact (@measurable_normed_total_add R X E N hN phi hphi _ _ (hA j hj) hAs).
  + exact (@vector_lone_approximable_add R X E N hN phi hphi G hGadd hGA
      _ _ (hA j hj) hAs (ha j hj) has).
Qed.

(** Source for [daniell_vector_finite_image_density]: the
    approximation of xi = sum t_i y_i by eta = sum h_i y_i
    in Federer 2.5.12, p. 105. The nonzero fibres of any
    summable finite-image function have finite measure; thus this
    form also works without first restricting to a finite-measure
    support. That strengthens the intermediate approximation step. *)
Theorem daniell_vector_finite_image_density (f : X -> real_norm_metric_space hN) :
  is_measure_lp_function phi 1 (partial_function_total f) ->
  finite_set (f @` setT) -> (forall x, D (f x)) ->
  is_vector_lone_approximable N phi G f.
Proof.
move=> hf hfin hDf.
pose C := fset_set (f @` setT).
pose S y := partial_function_preimage (partial_function_total f) [set y].
pose s y := @CharacteristicFunction.value R X (S y).
have hs y := @CharacteristicFunction.laws R X (S y).
pose u y x := (s y x *: y : real_norm_metric_space hN).
have hS y : measure_measurable phi (S y).
  apply: (@measurable_function_borel_preimage R X
    [the topologicalType of real_norm_metric_space hN] phi hphi
    (partial_function_total f) hf.2.1.1).
  apply: closed_borel_set; apply: accessible_closed_set1.
  apply: hausdorff_accessible; exact: metric_hausdorff.
have huA y : is_measurable_normed_function phi (partial_function_total (u y)).
  exact (@measurable_normed_characteristic_piece R X E N hN phi hphi (S y)
    (s y) (fun _ => y) (hs y) (hS y)
    (@measurable_normed_total_constant R X E N hN phi hphi y)).
have hu y : y \in (C : seq E) -> is_vector_lone_approximable N phi G (u y).
  move=> hyC.
  have hyim : (f @` setT) y.
    move: hyC; rewrite /C in_fset_set //; exact: set_mem.
  have [x _ hxy] := hyim.
  have hyD : D y by rewrite -hxy; exact: hDf.
  apply: (@daniell_vector_characteristic_approximation (S y) (s y) y (hs y) (hS y) _ hyD).
  move=> hy0; exact (@measure_lp_nonzero_fibre_finite R X E N hN phi hphi
    1 (partial_function_total f) y hf hy0).2.
have [hA ha] := @daniell_vector_finite_sum_approximation E (C : seq E) u
  (fun y _ => huA y) hu.
have he : (fun x => \sum_(y <- C) u y x)=f.
  apply: funext=> x.
  have hxC : f x \in (C : seq E).
    rewrite /C in_fset_set //; apply/mem_set; by exists x.
  have hcx : s (f x) x = 1.
    apply: (characteristic_on_set (hs (f x))); exists (f x); by split.
  have hc0 y : y != f x -> s y x = 0.
    move=> hy; apply: (characteristic_off_set (hs y))=> [[z [hz he]]].
    apply: (negP hy); apply/eqP; by rewrite -(hz : f x=z) in he; symmetry.
  exact (@finite_delta_vector_sum R E (C : seq E) (f x) (fun y => s y x)
    (fset_uniq C) hxC hcx hc0).
by rewrite he in ha.
Qed.
End Density.
