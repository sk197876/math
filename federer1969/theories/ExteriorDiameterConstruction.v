(** Private existence witness for the exterior-product supremum in Federer
    (1969), 2.10.3, p. 171. Reuse the abstract sealed extended supremum, and
    expose only the new diameter specification through a separate opaque
    interface. Source context: ExteriorDiameterUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations ExtendedSupremumSealed ExteriorDiameterUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [exterior_diameter_exists]: supporting
    existence of the possibly infinite supremum in Federer
    2.10.3, p. 171. The value set contains zero;
    the nonempty positive-degree case agrees with the
    printed value set by a separately proved lemma. *)
Theorem exterior_diameter_exists (R : realType) (n m : nat) (A : set (R_n R n)) :
  exists d, is_exterior_diameter m A d.
Proof.
have hne : exterior_diameter_values m A !=set0 by exists 0; left.
exists (@ExtendedSupremum.value R (exterior_diameter_values m A) hne).
exact: ExtendedSupremum.laws.
Qed.
