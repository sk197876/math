(** Federer (1969), 3.4.5, pp. 319–320:
    intersecting an original set with an actual neighbourhood
    does not change its germ. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_neighbourhood_intersection]: the
    original neighbourhood equivalence used for all analytic
    variety germs, 3.4.5, pp. 319–320. *)
Lemma set_germ_neighbourhood_intersection (X:topologicalType) (a:X) (U S:set X):
  open U ->U a ->set_germ a (U `&` S)=set_germ a S.
Proof.
move=>hU ha;apply/set_germ_equality_original;exists U;split;first exact:hU.
split;first exact:ha.
apply/seteqP;split.
- by move=>x [[hu hs] hu'];split.
- by move=>x [hs hu];split;first split.
Qed.
