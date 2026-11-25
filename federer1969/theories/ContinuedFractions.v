(** Federer (1969), 2.2.9, p. 65, final continued-fraction comparison: the
    limit of the displayed ordinary finite fractions is a homeomorphism from
    the positive- integer sequence space onto the irrational points of
    (0,1). This public module uses only the sealed limit and homeomorphism
    laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import SequenceSpace RealMetricBackground RationalRealUP
  HomeomorphismOnto FiniteContinuedFractions ContinuedFractionLimitUP ContinuedFractionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continued_fraction_map]: direct classical map
    mentioned in Federer 2.2.9, p. 65, exposed
    through its opaque existence witness and ordinary-limit laws. *)
Definition continued_fraction_map (R : realType) :
    positive_sequence_space R -> real_line_metric R := @ContinuedFraction.value R.
Arguments continued_fraction_map {R} n.

(** Source for [continued_fraction_map_limit]: direct convergence
    of every ordinary-digit truncation to the classical map in
    Federer 2.2.9, p. 65. *)
Theorem continued_fraction_map_limit (R : realType) :
  is_continued_fraction_map (@continued_fraction_map R).
Proof. exact: ContinuedFraction.laws. Qed.

(** Source for [continued_fraction_irrational_homeomorphism]:
    direct classical homeomorphism assertion of Federer 2.2.9,
    p. 65, with ordinary integer-ratio irrationality. *)
Theorem continued_fraction_irrational_homeomorphism (R : realType) :
  is_homeomorphism_onto (@irrational_unit_interval R : set (real_line_metric R)) (@continued_fraction_map R).
Proof. exact: ContinuedFraction.homeomorphism. Qed.

(** Source for [continued_fraction_map_irrational]: direct target
    assertion for the continued-fraction map in Federer 2.2.9,
    p. 65: every value is irrational and strictly
    between zero and one. *)
Lemma continued_fraction_map_irrational (R : realType) (n : positive_sequence_space R) :
  irrational_unit_interval (continued_fraction_map n).
Proof.
rewrite -(homeomorphism_onto_image (continued_fraction_irrational_homeomorphism R)).
by exists n.
Qed.

(** Source for [continued_fraction_map_injective]: supporting
    uniqueness of positive-digit expansions for irrational points
    in the homeomorphism of Federer 2.2.9, p. 65. *)
Lemma continued_fraction_map_injective (R : realType) : injective (@continued_fraction_map R).
Proof. exact: homeomorphism_onto_injective (continued_fraction_irrational_homeomorphism R). Qed.

(** Source for [irrational_continued_fraction_unique_expansion]:
    direct bijectivity consequence of the classical homeomorphism
    in Federer 2.2.9, p. 65: each irrational
    point in (0,1) has exactly one infinite positive-digit expansion. *)
Theorem irrational_continued_fraction_unique_expansion (R : realType) (x : R) :
  irrational_unit_interval x -> exists! n : positive_sequence_space R,
    continued_fraction_map n = x.
Proof.
move=> hx.
rewrite -(homeomorphism_onto_image (continued_fraction_irrational_homeomorphism R)) in hx.
have [n _ hn] := hx; exists n; split=> // m hm.
apply: continued_fraction_map_injective; exact: eq_trans hn (esym hm).
Qed.
