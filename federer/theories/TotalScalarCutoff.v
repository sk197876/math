(** Federer (1969), 2.5.10, p. 101: functions supported on one measurable
    piece, using the zero extension from 2.4.10, p. 85. The characteristic
    function is obtained from the project's sealed interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CharacteristicFunctionUP CharacteristicFunctionSealed
  ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [total_scalar_cutoff]: supporting total real form
    of Federer's zero extension, 2.4.10, p. 85, used in
    the local functional of 2.5.10, p. 101. *)
Definition total_scalar_cutoff (R : realType) (X : Type) (B : set X) (f : X -> R) :=
  fun x => f x * @CharacteristicFunction.value R X B x.

(** Source for [total_scalar_cutoff_on]: direct agreement on the
    piece in Federer 2.4.10, p. 85; supporting 2.5.10, p. 101. *)
Lemma total_scalar_cutoff_on (R : realType) (X : Type) (B : set X) (f : X -> R) x :
  B x -> total_scalar_cutoff B f x=f x.
Proof. move=> hx; by rewrite /total_scalar_cutoff (characteristic_on_set (@CharacteristicFunction.laws R X B) hx) mulr1. Qed.

(** Source for [total_scalar_cutoff_off]: direct zero value off
    the piece in Federer 2.4.10, p. 85; supporting 2.5.10, p. 101. *)
Lemma total_scalar_cutoff_off (R : realType) (X : Type) (B : set X) (f : X -> R) x :
  ~ B x -> total_scalar_cutoff B f x=0.
Proof. move=> hx; by rewrite /total_scalar_cutoff (characteristic_off_set (@CharacteristicFunction.laws R X B) hx) mulr0. Qed.

(** Source for [total_scalar_cutoff_add]: supporting linearity
    of the local functional in Federer 2.5.10, p. 101. *)
Lemma total_scalar_cutoff_add (R : realType) (X : Type) (B : set X) (f g : X -> R) :
  total_scalar_cutoff B (fun x => f x+g x)=
    (fun x => total_scalar_cutoff B f x+total_scalar_cutoff B g x).
Proof. by apply: funext=> x; rewrite /total_scalar_cutoff mulrDl. Qed.

(** Source for [total_scalar_cutoff_scale]: supporting scalar
    linearity of the local functional in Federer 2.5.10, p. 101. *)
Lemma total_scalar_cutoff_scale (R : realType) (X : Type) (B : set X) (f : X -> R) (c : R) :
  total_scalar_cutoff B (fun x => c * f x)=(fun x => c * total_scalar_cutoff B f x).
Proof. by apply: funext=> x; rewrite /total_scalar_cutoff mulrA. Qed.

(** Source for [total_scalar_cutoff_absolute]: supporting equality
    of L1 norms for the restricted measure in Federer 2.5.10, p. 101. *)
Lemma total_scalar_cutoff_absolute (R : realType) (X : Type) (B : set X) (f : X -> R) :
  (fun x => `|total_scalar_cutoff B f x|)=total_scalar_cutoff B (fun x => `|f x|).
Proof.
apply: funext=> x; case: (pselect (B x))=> hx.
- by rewrite !total_scalar_cutoff_on.
- by rewrite !total_scalar_cutoff_off // normr0.
Qed.

(** Source for [total_scalar_cutoff_integrand_graph]: supporting
    identification of the total real cutoff with the abstract partial
    zero extension, Federer 2.4.10, p. 85, used in 2.5.10, p. 101. *)
Lemma total_scalar_cutoff_integrand_graph (R : realType) (X : Type) (B : set X) (f : X -> R) x z :
  partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) B (real_total_integrand f)) x z <->
    partial_function_graph (real_total_integrand (total_scalar_cutoff B f)) x z.
Proof.
rewrite real_total_integrand_graph; case: (pselect (B x))=> hx.
- rewrite (total_scalar_cutoff_on f hx) (partial_function_zero_extension_on 0 (real_total_integrand f) z hx).
  exact: real_total_integrand_graph.
- rewrite (total_scalar_cutoff_off f hx) (partial_function_zero_extension_off 0 (real_total_integrand f) z hx).
  split=> h; exact: esym h.
Qed.
