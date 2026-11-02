(** Federer (1969), 2.2.3, p. 62, final paragraph: regularisation by the
    infimum over Borel supersets. The construction is sealed; mathematical
    consequences use its greatest-lower-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import TopologicalBorel ExtendedRealBounds MeasureUP BorelRegularisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_regularisation_exists]: Federer
    2.2.3, p. 62, final display; the extended-real infimum witnesses
    the abstract regularisation specification. Its order laws hold
    even before assuming that the input function is a measure. *)
Lemma borel_regularisation_exists (R : realType) (I : topologicalType)
    (mu : set I -> \bar R) : exists nu, is_borel_regularisation mu nu.
Proof.
exists (fun A => extended_real_inf [set t | exists B,
  A `<=` B /\ borel_set B /\ t = mu B]).
constructor.
- move=> A B hAB hB; apply: extended_real_inf_lower.
  exists B; by split=> //; split.
- move=> A c hc; apply: extended_real_inf_greatest=> t [B [hAB [hB ->]]].
  exact: hc B hAB hB.
Qed.
