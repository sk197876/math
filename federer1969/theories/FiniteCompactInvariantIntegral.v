(** Federer (1969), 3.2.13, p. 251: a finite invariant
    Borel measure on a compact homogeneous space supplies an
    invariant Daniell integral. This connects geometric sphere
    invariance with the uniqueness theorem 2.7.11(2), p. 128. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MeasureUP MeasureBasic MeasurePushforward BorelRegularMeasureUP TopologicalBorel
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportSummability
  SummableRealFunctionUP RealIntegralFunctionalUP RealIntegralFunctional
  MonotoneDaniellIntegralUP DaniellIntegralNegation CovariantIntegralUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralUniqueness
  InjectivePushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_borel_compact_tests_summable]: compact
    continuous tests are summable for a finite Borel regular measure,
    by 2.5.13, p. 106, used for the sphere in Federer
    3.2.13, p. 251. *)
Lemma finite_borel_compact_tests_summable (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (hB:is_borel_regular_measure mu):
  (mu setT < +oo)%E ->@compactly_supported_continuous_functions R X `<=` summable_real_functions mu.
Proof.
move=>hFin u hu.
apply:(@compactly_supported_summable R X mu hm
  (fun B hBor=>borel_regular_borel_measurable hm hB hBor) _ u hu)=>K hK.
exact:le_lt_trans (measure_mono hm (@subsetT _ K)) hFin.
Qed.

(** Source for [finite_compact_invariant_integral_exists]: the
    geometric invariant sphere measure gives an invariant integral
    on continuous tests, Federer 3.2.13, p. 251, using
    2.5.1, p. 92, and 2.7.1, p. 122. The integral
    functional is obtained from the existing sealed interface. *)
Theorem finite_compact_invariant_integral_exists (R:realType) (X:topologicalType) (G:Type)
    (A:G->X->X) (mu:set X->\bar R):
  compact [set:X] ->is_measure mu ->is_borel_regular_measure mu ->(mu setT < +oo)%E ->
  (forall g,continuous (A g)) ->(forall g,injective (A g)) ->
  (forall g,measure_pushforward (A g) mu=mu) ->
  exists L:(X->R)->R,is_real_integral_functional mu (@compactly_supported_continuous_functions R X) L /\
    is_invariant_integral A L.
Proof.
move=>hX hm hB hFin hCont hInj hPush.
pose hSum:=finite_borel_compact_tests_summable hm hB hFin.
pose L:=@lattice_measure_integral R X mu (@compactly_supported_continuous_functions R X) hSum.
have hRep:=@lattice_measure_integral_specification R X mu (@compactly_supported_continuous_functions R X) hSum.
have hMon:=@summable_sublattice_integral_laws R X mu hm (@compactly_supported_continuous_functions R X)
  hSum (@compactly_supported_continuous_functions_lattice R X).
exists L; split=>//; constructor; first exact:monotone_daniell_is_daniell hMon.
move=>u g hu; rewrite mul1r.
have hComp:compactly_supported_continuous_functions (u\o A g).
  split.
  - move=>x; exact:(continuous_comp (hCont g x) (hu.1 (A g x))).
  - exact:(subclosed_compact (@real_function_support_closed R X _) hX (@subsetT _ _)).
have hIff:=@injective_pushforward_integral_iff R X X mu hm (A g)
  (real_total_integrand u) (hInj g) (L u)%:E.
rewrite (hPush g) in hIff.
have hActual:is_measure_integral mu (real_total_integrand (u\o A g)) (L u)%:E.
  apply:(measure_integral_graph_equivalent _ (hIff.2 (hRep u hu)))=>x y.
  by [].
exact:EFin_inj (measure_integral_unique (hRep _ hComp) hActual).
Qed.
