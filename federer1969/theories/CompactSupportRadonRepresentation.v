(** Federer (1969), 2.5.14, pp. 107–108: every monotone Daniell integral on
    K(X), for locally compact Hausdorff X, is represented by a Radon
    measure. All witnesses here come from sealed interfaces. This theorem
    concerns the scalar representation; the later paragraph's modification
    of the vector theorem 2.5.12 is separate. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice
  CompactOpenContentUP CompactOpenContentSealed CompactOpenContentCover CompactOpenEnvelopeRadon
  CompactOpenEnvelopeRepresentation OpenCoverEnvelope MonotoneDaniellIntegralUP MonotoneDaniellRepresentation
  RegularDaniellRepresentation RealIntegralFunctionalUP MeasureUP RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_support_radon_representation]: the scalar Radon
    representation asserted in Federer 2.5.14, p. 107, proved on pp. 107–108
    No countable-base or sigma-finiteness assumption is added. Every
    compactly supported continuous real function has its actual finite
    integral equal to A(f). *)
Theorem compact_support_radon_representation (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) : hausdorff_space X -> locally_compact (@setT X) ->
  is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  exists nu : set X -> \bar R, is_measure nu /\ is_radon_measure nu /\
    is_real_integral_functional nu (@compactly_supported_continuous_functions R X) A.
Proof.
move=> hh hl hD.
have hL := @compactly_supported_continuous_functions_lattice R X.
pose mu := @monotone_daniell_measure R X _ A hL hD.
have hm := @monotone_daniell_measure_is_measure R X _ A hL hD.
have hA := @monotone_daniell_measure_represents R X _ A hL hD.
have hne : exists f : X -> R, compactly_supported_continuous_functions f.
  exists (fun _ => 0%R); exact: compactly_supported_zero_function.
have hr := @monotone_daniell_measure_lattice_regular R X _ A hL hD hne.
pose a := @CompactOpenContent.value R X A.
have ha := @CompactOpenContent.laws R X A.
have hc := @compact_open_content_is_open_cover_content R X A a hD ha hh hl.
pose nu := @open_cover_envelope R X a hc.
have hn := @open_cover_envelope_specification R X a hc.
have hnm := @open_cover_envelope_is_measure R X a hc.
exists nu; split=> //; split.
- exact: (@compact_open_envelope_radon R X mu nu A a hm hnm hD hA hr ha hn hh hl).
- exact: (@compact_open_envelope_represents R X mu nu A a hm hnm hD hA hr ha hc hn hh hl).
Qed.
