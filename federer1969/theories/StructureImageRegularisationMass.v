(** Federer (1969), 3.3.7, p. 294: the Borel regularisation
    has the exact original source mass on its original image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasurePushforward
  TopologicalBorel BorelRegularisationUP BorelRegularisationBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_image_regularisation_mass]: the exact identity
    phi(A)=psi[p(A)] in Federer 3.3.7, p. 294. The supporting general
    image version uses only the independent Borel-infimum laws. The
    regularisation dominates the actual image measure and is bounded
    above by its mass on the Borel whole target. Original A and f(A)
    need not be measurable, and infinite masses are included. *)
Theorem structure_image_regularisation_mass (R:realType) (X:choiceType)
    (Y:topologicalType) (phi:set X-> \bar R) (A:set X) (f:X->Y)
    (psi:set Y-> \bar R):
  is_measure phi ->is_borel_regularisation (measure_pushforward f (measure_restrict phi A)) psi ->
  phi A=psi (f @` A).
Proof.
move=>hPhi hRegularisation.
pose mu:=measure_pushforward f (measure_restrict phi A).
have hMu:is_measure mu:=measure_pushforward_is_measure f (measure_restrict_is_measure hPhi A).
have hImage:A `&` f @^-1` (f @` A)=A.
  apply/seteqP; split; first by move=>x [hx _].
  move=>x hx; split; first exact:hx.
  by exists x.
have hImageMass:mu (f @` A)=phi A by rewrite /mu /measure_pushforward /measure_restrict hImage.
have hTotal:mu setT=phi A by rewrite /mu /measure_pushforward /measure_restrict preimage_setT setIT.
apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite -hImageMass.
  exact:(borel_regularisation_dominates hMu hRegularisation (f @` A)).
- rewrite -hTotal.
  exact:(@borel_regularisation_lower R Y mu psi hRegularisation (f @` A) setT
    (subsetT _) (open_borel_set (@openT Y))).
Qed.
