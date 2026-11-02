(** Federer (1969), 2.5.14, pp. 107–108: the open envelope Phi is Radon. We
    establish these laws before identifying all test integrals, using the
    supremum/infimum laws directly. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportMeasureFinite CompactOpenContentUP
  CompactOpenContentCover CompactOpenContentMeasureBound CompactOpenEnvelopeMeasurability
  OpenCoverContentUP OpenCoverContentLaws FunctionLatticeRegularityUP RealIntegralFunctionalUP
  MonotoneDaniellIntegralUP MeasureUP MeasureBasic RadonMeasureUP ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_open_test_support_measure_bound]: the lower bound
    lambda(f) <= Phi(support f) for tests bounded by one, supporting inner
    regularity in Federer 2.5.14, p. 108 The bound is derived from the
    defining open costs before using any integral representation for Phi. *)
Lemma compact_open_test_support_measure_bound (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (a nu : set X -> \bar R)
    (ha : is_compact_open_content A a) (hn : is_open_cover_envelope a nu) V f :
  is_compact_open_test_function V f -> (A f)%:E <= nu (real_function_support f).
Proof.
move=> [hf [hb hs]]; apply: (open_cover_envelope_greatest hn)=> W hW hSW.
apply: (extended_real_supremum_upper (ha W hW)); exists f; split=> //; split=> //; by split.
Qed.

(** Source for [compact_open_envelope_radon]: Radon regularity of Phi in
    Federer 2.5.14, pp. 107–108 Neither a countable base nor
    sigma-finiteness is assumed. Identification of the integral on K(X) is a
    separate conclusion. *)
Theorem compact_open_envelope_radon (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (A : (X -> R) -> R) (a : set X -> \bar R)
    (hm : is_measure mu) (hnm : is_measure nu)
    (hD : is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A)
    (hr : is_function_lattice_regular (@compactly_supported_continuous_functions R X) mu)
    (ha : is_compact_open_content A a) (hn : is_open_cover_envelope a nu) :
  hausdorff_space X -> locally_compact (@setT X) -> is_radon_measure nu.
Proof.
move=> hh hl.
have hc := @compact_open_content_is_open_cover_content R X A a hD ha hh hl.
have hval := @open_cover_envelope_open_value R X a nu hc hn.
constructor=> //.
- move=> K hK; exact (le_lt_trans
    (@compact_open_envelope_below_regular_measure R X mu nu A a hm hA hr ha hn K)
    (@compact_support_representing_measure_compact_finite R X mu A hm hA hh hl K hK)).
- move=> V hV; exact: (@compact_open_envelope_open_measurable R X A a nu hD ha hn hnm V hV).
- move=> V hV c hbound; rewrite (hval V hV).
  apply: (extended_real_supremum_least (ha V hV))=> b [f [hf ->]].
  exact (le_trans (@compact_open_test_support_measure_bound R X A a nu ha hn V f hf)
    (hbound _ hf.1.2 hf.2.2)).
- move=> S c hbound; apply: (open_cover_envelope_greatest hn)=> V hV hSV.
  rewrite -(hval V hV); exact: hbound V hV hSV.
Qed.
