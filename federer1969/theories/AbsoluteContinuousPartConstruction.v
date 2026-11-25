(** Private existence proof for the infimum in Federer (1969), 2.9.1, p.
    152. The extended-real infimum supplies a witness for the abstract
    specification; no project axiom is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import TopologicalBorel ExtendedRealBounds AbsoluteContinuousPartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_part_exists]: existence of the abstract infimum
    in Federer 2.9.1, p. 152 The witness remains in this opaque proof and is
    exposed through sealing. *)
Lemma continuous_part_exists (R : realType) (X : topologicalType)
    (phi psi : set X -> \bar R) :
  exists gamma, is_absolutely_continuous_part phi psi gamma.
Proof.
exists (fun A => extended_real_inf [set t | exists B,
  borel_set B /\ phi (A `\` B) = 0 /\ t = psi B]).
constructor.
- move=> A B hB hz; apply: extended_real_inf_lower.
  exists B; by split=> //; split.
- move=> A c hc; apply: extended_real_inf_greatest=> t [B [hB [hz ->]]].
  exact: hc B hB hz.
Qed.
