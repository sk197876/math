(** Private existence witness for the infimum formula in Federer (1969),
    2.5.2, p. 92 The already sealed extended-real infimum supplies the
    witness; all later arguments use its envelope laws. Source conventions:
    DaniellCoverUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import DaniellCoverUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_cover_envelope_exists]: existence of the
    infimum-defined set function in Federer 2.5.2, p. 92 This does not yet
    assert the measure laws. In particular, the empty lattice requires a
    separate representation case before this envelope is used. *)
Lemma daniell_cover_envelope_exists (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) :
  exists mu, is_daniell_cover_envelope L A mu.
Proof.
pose costs S := [set c | exists f, is_daniell_suiting_sequence L S f /\ is_daniell_sequence_cost A f c].
exists (fun S => extended_real_inf (costs S)); constructor.
- move=> S f c hs hc; apply: extended_real_inf_lower; by exists f.
- move=> S b hb; apply: extended_real_inf_greatest=> c [f [hs hc]].
  exact: hb f c hs hc.
Qed.
