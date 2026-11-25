(** Private existence construction for the fixed-family infimum in Federer
    (1969), 2.10.1, pp. 169–170, used for the 2.3.8 counterexample. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import NonnegativeSum ExtendedRealBounds CountableCoverEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_cover_envelope_exists]: existence of the
    covering infimum from Federer 2.10.1, p. 170,
    using the extended-real order completeness of 2.1.1, p. 51. *)
Lemma countable_cover_envelope_exists (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) :
  exists nu, is_countable_cover_envelope S cost nu.
Proof.
exists (fun A => extended_real_inf [set t | exists G : set J,
  countable G /\ A `<=` \bigcup_(j in G) S j /\ t = nonnegative_sum G cost]).
constructor.
- move=> A G hc hcov; apply: extended_real_inf_lower; exists G; by split=> //; split.
- move=> A b hb; apply: extended_real_inf_greatest=> t [G [hc [hcov ->]]]; exact: hb.
Qed.
