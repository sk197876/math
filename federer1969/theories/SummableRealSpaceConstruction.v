(** Federer (1969), 2.6.4, pp. 118–119: the vector spaces of total-domain
    summable real functions in the tensor diagram. Erratum p. 2, book p. 119
    lines 3, 4, 6, requires the total-domain notation. We keep literal
    functions, not classes modulo null functions. The subspace laws follow
    from 2.4.4(3)–(4), p. 82. his Chapter 18 does not state this tensor
    diagram. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import ModuleQuotient SubspaceCarrier MeasureUP MeasureIntegralUP
  SummableRealFunctionUP SummableRealArithmetic LatticeL1ApproximationLaws
  TotalLoneSummability TotalScalarLpUP SummableRealSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Space.
Variable R : realType.
Variable X : choiceType.
Variable mu : set X -> \bar R.
Variable hm : is_measure mu.
Local Notation F := (GRing.Lmodule.clone R (X -> R^o) _).

(** Source for [summable_carrier_subspace]: supporting vector-space
    laws for the total-domain L1 space in Federer 2.6.4,
    pp. 118–119, with his erratum p. 2, book p. 119
    lines 3, 4, 6. This supplies a carrier for the tensor product. *)
Definition summable_carrier_subspace : subspace F.
Proof.
refine (@Subspace R F (summable_real_functions mu) _ _ _).
- exists 0; exact: real_total_zero_integral hm.
- move=> f g hf hg; exact (@summable_real_add R X mu hm f g hf hg).
- move=> c f hf; exact (@summable_real_scale R X mu hm f c hf).
Defined.

(** Source for [summable_carrier_space]: the total-domain L1 vector
    space in the corrected diagram of Federer 2.6.4, p. 119.
    Membership is specified by existence of a finite actual integral. *)
Definition summable_carrier_space : lmodType R :=
  [the lmodType R of subspace_space summable_carrier_subspace].

(** Source for [summable_carrier_value]: supporting injective inclusion
    of the total-domain space in real functions for Federer 2.6.4,
    pp. 118–119. Values on null sets are retained. *)
Definition summable_carrier_value : {linear summable_carrier_space -> F} :=
  GRing.Linear.clone _ _ _ _ (@subspace_val R F summable_carrier_subspace) _.

(** Source for [summable_carrier_value_injective]: supporting literal
    function equality for the monomorphism in Federer 2.6.4,
    p. 118. No almost-everywhere quotient is introduced. *)
Lemma summable_carrier_value_injective : injective summable_carrier_value.
Proof. exact: subspace_val_injective. Qed.

(** Source for [summable_carrier_value_summable]: supporting membership
    of each carrier element in the summable space of Federer 2.6.4,
    p. 118. *)
Lemma summable_carrier_value_summable f : summable_real_functions mu (summable_carrier_value f).
Proof. exact (@subspace_valP R F summable_carrier_subspace f). Qed.

(** Source for [summable_carrier_value_lone]: compatibility with the
    existing total-domain L1 definition, Federer 2.4.12, p. 86,
    used in the corrected tensor diagram of 2.6.4, p. 119. *)
Lemma summable_carrier_value_lone f : total_scalar_lp mu 1 (summable_carrier_value f).
Proof. exact (@summable_real_total_lone R X mu hm _ (summable_carrier_value_summable f)). Qed.
(** Source for [summable_carrier_laws]: the constructed carrier
    satisfies the abstract total-domain L1 specification for Federer
    2.6.4, pp. 118–119, after his erratum p. 2. *)
Lemma summable_carrier_laws : is_summable_real_space mu summable_carrier_value.
Proof.
split; first exact: summable_carrier_value_injective.
move=> f; split.
- move=> hf; exists (@subspace_lift R F summable_carrier_subspace f hf); by [].
- move=> [g <-]; exact: summable_carrier_value_summable.
Qed.
End Space.
