(** Private witness for the supporting four-digit reindexing of the
    classical continued fraction in Federer (1969), 2.2.9, p. 65. Compose
    the already proved countable-pair bijection twice. Later proofs use only
    the inverse laws. Source context and attribution:
    NaturalQuadruplingUP.v. *)
From mathcomp Require Import all_boot.
From Federer Require Import NaturalPairing NaturalQuadruplingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [natural_quadrupling_exists]: supporting existence
    of the inverse-law specification for the grouping in Federer
    2.2.9, p. 65. No particular pairing algorithm
    is exposed to the mathematical development. *)
Lemma natural_quadrupling_exists : exists e d, is_natural_quadrupling e d.
Proof.
have [e [d [hed hde]]] := natural_pairing_exists.
pose E (p : (nat * nat) * (nat * nat)) := e (e p.1,e p.2).
pose D n := (d (d n).1,d (d n).2).
exists E,D; constructor.
- by move=> [p q]; rewrite /E /D hed /= !hed.
- move=> n; rewrite /E /D /= !hde.
  by case he : (d n)=> [a b]; rewrite -he hde.
Qed.
