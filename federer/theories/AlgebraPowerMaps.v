(** Federer (1969), 1.9.4, p. 43: the diagonal is a unit-preserving algebra
    homomorphism, so it carries powers to powers. These supporting laws
    apply to any such algebra map. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP AlgebraPowers DividedBinomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [algebra_hom_power]: Federer 1.9.4, p. 43,
    supporting consequence of the algebra-map definition: a unital
    homomorphism preserves every nonnegative power. *)
Lemma algebra_hom_power (K : fieldType) (A B : algebra K)
    (f : algebra_map A B) x m :
  f (@algebra_power K A x m) = @algebra_power K B (f x) m.
Proof.
elim: m=> [|m ih]; first exact: algebra_map_one.
by rewrite /= algebra_map_mul ih.
Qed.

(** Source for [algebra_hom_divided_power]: Federer 1.9.4,
    p. 43, supporting consequence for divided powers: linearity
    also preserves the scalar factor given by the inverse factorial. *)
Lemma algebra_hom_divided_power (K : fieldType) (A B : algebra K)
    (f : algebra_map A B) x m :
  f (@divided_power K A x m) = @divided_power K B (f x) m.
Proof. by rewrite /divided_power linearZ algebra_hom_power. Qed.
