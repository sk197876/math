(** Federer (1969), 2.5.20, p. 114: gamma+ + gamma- is the monotone Daniell
    functional pushed forward in the final sentence. The existing variations
    are specified on K(Y)+ by 2.5.5, pp. 96–97. Here their sum is extended
    to K(Y) by positive and negative parts, so the image functional is
    defined on the entire displayed domain. Source context:
    WeightedDaniellVariation.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice
  FunctionLatticeUP MonotoneDaniellIntegralUP DaniellIntegralUP DaniellIntegralNegation
  DaniellVariationUP DaniellVariationBounds DaniellVariationFunctionals
  PositiveDifferenceFunctional CompactPositiveConeExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_daniell_total_variation]: the sum
    gamma+ + gamma- on K(Y) in Federer 2.5.20, p. 114.
    Positive-cone values from 2.5.5, pp. 96–97, are
    extended by the parts identity of 2.5.1, p. 91. *)
Definition compact_daniell_total_variation (R : realType) (Y : Type)
    (P Q : (Y -> R) -> R) := positive_difference_functional (fun f => P f+Q f).

(** Source for [compact_daniell_total_variation_parts]:
    extending the sum gives the sum of the individual
    extensions, supporting the notation gamma+ + gamma-
    in Federer 2.5.20, p. 114. *)
Lemma compact_daniell_total_variation_parts (R : realType) (Y : Type)
    (P Q : (Y -> R) -> R) (f : Y -> R) :
  compact_daniell_total_variation P Q f=
    positive_difference_functional P f+positive_difference_functional Q f.
Proof. rewrite /compact_daniell_total_variation /positive_difference_functional; lra. Qed.

(** Source for [compact_daniell_total_variation_laws]: the
    monotone Daniell laws of gamma+ + gamma-, used in
    the last sentence of Federer 2.5.20, p. 114,
    with agreement on K(Y)+. They follow from 2.5.5,
    pp. 96–97, and the compact-support extension in
    2.5.14, p. 108. *)
Theorem compact_daniell_total_variation_laws (R : realType) (Y : topologicalType)
    (A P Q : (Y -> R) -> R) :
  hausdorff_space Y -> locally_compact (@setT Y) ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  is_daniell_positive_variation (@compactly_supported_continuous_functions R Y) A P ->
  is_daniell_negative_variation (@compactly_supported_continuous_functions R Y) A Q ->
  is_monotone_daniell_integral (@compactly_supported_continuous_functions R Y)
    (compact_daniell_total_variation P Q) /\
  forall f, positive_function_lattice (@compactly_supported_continuous_functions R Y) f ->
    compact_daniell_total_variation P Q f= P f+Q f.
Proof.
move=> hh hl hA hP hQ.
have hL := @compactly_supported_continuous_functions_lattice R Y.
have hPm := positive_variation_monotone_daniell hL hA hP.
have hQm := negative_variation_monotone_daniell hL hA hQ.
apply: (@compact_positive_difference_daniell R Y (fun f => P f+Q f) hh hl).
- move=> f g hf hg.
  rewrite (monotone_daniell_integral_add hPm hf hg) (monotone_daniell_integral_add hQm hf hg).
  lra.
- move=> c f hc hf.
  rewrite (monotone_daniell_integral_scale hPm hc hf) (monotone_daniell_integral_scale hQm hc hf) mulrDr.
  by [].
- move=> f hf; apply: addr_ge0.
  + exact (@daniell_positive_variation_nonnegative R Y
      (@compactly_supported_continuous_functions R Y) A P hL hA hP f hf).
  + exact (@daniell_positive_variation_nonnegative R Y
      (@compactly_supported_continuous_functions R Y) (fun f => - A f) Q hL
      (daniell_integral_negate hL hA) hQ f hf).
Qed.
