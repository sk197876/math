(** Federer (1969), 3.2.46, p. 281: translating a
    curve parameter leaves its velocity unchanged, supporting
    concatenation and its actual integral identity. This follows
    directly from the two-sided quotient of 2.9.22, p. 167. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [normed_curve_parameter_translation_iff]:
    the actual derivative graph under a parameter translation,
    supporting the concatenation argument in Federer 3.2.46,
    p. 281. Both directions retain absent derivatives. *)
Lemma normed_curve_parameter_translation_iff (R : realType) (E : lmodType R)
    (N : E -> R) (C : R -> E) (d t : R) v :
  has_normed_curve_derivative N (fun s=>C (s+d)) t v <->
  has_normed_curve_derivative N C (t+d) v.
Proof.
have he : (fun h=>h^-1 *: (C (t+h+d)-C (t+d))) =
    (fun h=>h^-1 *: (C (t+d+h)-C (t+d))).
  by apply: funext=> h; rewrite (addrAC t h d).
by rewrite /has_normed_curve_derivative he.
Qed.
