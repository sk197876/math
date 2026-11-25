(** Federer (1969), 2.5.14, p. 107, representation by the Radon envelope
    Phi. We transfer finite measurable sets through the regular F2 hulls,
    then integrals through 2.3.3 and 2.4.8. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportLevels CompactSupportIntegralTransfer
  CompactOpenContentUP CompactOpenContentLevelAgreement CompactOpenContentMeasureBound
  CompactOpenEnvelopeMeasurability OpenCoverContentUP LatticeRegularMeasureTransfer
  FunctionLatticeLevelMeasurability FunctionLatticeRegularityUP RealIntegralFunctionalUP MonotoneDaniellIntegralUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_open_envelope_represents]: the identity integral f
    dPhi = lambda(f) for every f in K(X) in Federer 2.5.14, p. 107 The
    hypotheses describe the two measures by their laws and do not expose
    either construction. *)
Theorem compact_open_envelope_represents (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (A : (X -> R) -> R) (a : set X -> \bar R)
    (hm : is_measure mu) (hnm : is_measure nu)
    (hD : is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A)
    (hr : is_function_lattice_regular (@compactly_supported_continuous_functions R X) mu)
    (ha : is_compact_open_content A a) (hc : is_open_cover_content a)
    (hn : is_open_cover_envelope a nu) :
  hausdorff_space X -> locally_compact (@setT X) ->
  is_real_integral_functional nu (@compactly_supported_continuous_functions R X) A.
Proof.
move=> hh hl.
apply: (@compact_support_integral_transfer R X mu nu A hm hnm hA hD hh hl).
apply: (@lattice_regular_finite_measure_transfer R X _ mu nu hm hnm hr).
- exact: (@compact_open_envelope_below_regular_measure R X mu nu A a hm hA hr ha hn).
- apply: (@lattice_finite_hull_measure_transfer R X _ mu nu hm hnm)=> V hV; split.
  + exact: (@represented_lattice_increasing_level_measurable R X _ A mu hm hA V hV).
  + split.
    * exact: (@compact_open_envelope_open_measurable R X A a nu hD ha hn hnm V
        (@compact_support_increasing_level_open R X V hV)).
    * exact: (@compact_open_envelope_increasing_level_value R X mu nu A a hm hA ha hc hn hh hl V hV).
Qed.
