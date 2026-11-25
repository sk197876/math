(** Federer (1969), 4.1.19, p. 377: the full
    L1 extension uses the finite original integral
    seminorm on actual measurable fields. Almost-equal
    representatives need not be equal in this carrier. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ModuleQuotient
  SubspaceCarrier MeasureUP PartialFunctionBasic MeasurableNormedFunctionUP
  TotalMeasurableFunctionSpace MeasureLpNormTotal ExtendedSeminormUP
  LinearSubspaceRepresentationUP SummableFieldUP SummableFieldSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section SummableFieldLaws.
Variable R : realType.
Variable X : topologicalType.
Variable V : lmodType R.
Variable N : V -> R.
Variable hN : is_real_norm N.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Local Notation W := (@SummableField.space R X V N hN mu hm).
Local Notation inc := (@SummableField.inclusion R X V N hN mu hm).
Local Notation hW := (@SummableField.laws R X V N hN mu hm).
Local Notation L := (@total_measurable_lp_norm R X V N hN mu hm 1).

(** Source for [summable_field_value]: total values of
    the original finite L1 fields, 2.4.12, pp. 86–87,
    used for representation in 4.1.19, p. 377. *)
Definition summable_field_value (f : W) :
    X -> real_norm_metric_space hN := subspace_val (inc f).

(** Source for [summable_field_measurable]: fields in
    the L1 extension of Federer 4.1.19, p. 377,
    retain original normed measurability from 2.4.12. *)
Lemma summable_field_measurable (f : W) :
  is_measurable_normed_function mu
    (partial_function_total (summable_field_value f)).
Proof. exact: (subspace_valP (inc f)). Qed.

(** Source for [summable_field_finite]: the carrier
    retains the defining finite L1 value of 2.4.12,
    supporting Federer 4.1.19, p. 377. *)
Lemma summable_field_finite (f : W) : (L (inc f) < +oo)%E.
Proof.
exact: (@subspace_representation_member R
  (subspace_space (@total_measurable_normed_subspace R X V N hN mu hm)) W
  (@summable_field_subspace R X V N hN mu hm) inc hW f).
Qed.

(** Source for [summable_field_value_injective]: these
    are the actual raw representatives in the L1
    extension of Federer 4.1.19, p. 377, before
    taking almost-equality classes. *)
Lemma summable_field_value_injective : injective summable_field_value.
Proof.
move=> f g hEqual.
apply: (subspace_representation_injective hW).
apply: subspace_val_injective; exact: hEqual.
Qed.

(** Source for [summable_field_value_add]: addition of
    actual L1 fields, 2.4.12, pp. 86–87,
    supporting the extension in 4.1.19, p. 377. *)
Lemma summable_field_value_add (f g : W) :
  summable_field_value (f+g)%R =
    (fun x => (summable_field_value f x+summable_field_value g x)%R).
Proof. by rewrite /summable_field_value !linearD. Qed.

(** Source for [summable_field_value_scale]: scalar
    multiplication of actual L1 fields, 2.4.12,
    pp. 86–87, used in 4.1.19, p. 377. *)
Lemma summable_field_value_scale (c : R) (f : W) :
  summable_field_value (c*:f)%R =
    (fun x => (c*:summable_field_value f x)%R).
Proof. by rewrite /summable_field_value !linearZ. Qed.

(** Source for [summable_field_size]: the finite real
    value of the original L1 seminorm, 2.4.12,
    pp. 86–87, for the bounded-functional extension
    in Federer 4.1.19, p. 377. *)
Definition summable_field_size (f : W) : R := fine (L (inc f)).

(** Source for [summable_field_size_exact]: recover
    the original extended L1 value exactly, supporting
    the dual norm in Federer 4.1.19, p. 377. *)
Lemma summable_field_size_exact (f : W) :
  (summable_field_size f)%:E = L (inc f).
Proof.
rewrite /summable_field_size fineK //.
have hL := @total_measurable_lp_norm_seminorm R X V N hN mu hm 1 (lexx 1).
by rewrite (ge0_fin_numE (extended_seminorm_nonnegative hL (inc f)));
  exact: summable_field_finite.
Qed.

(** Source for [summable_field_size_seminorm]: the
    real L1 seminorm on actual finite representatives,
    2.4.12, pp. 86–87, supports Hahn–Banach in
    Federer 4.1.19, p. 377. No separated-norm
    conclusion is claimed on these raw fields. *)
Theorem summable_field_size_seminorm :
  is_real_seminorm summable_field_size.
Proof.
have hL := @total_measurable_lp_norm_seminorm R X V N hN mu hm 1 (lexx 1).
constructor.
- move=> f; apply: fine_ge0.
  exact: (extended_seminorm_nonnegative hL (inc f)).
- move=> c f.
  have he : L (inc (c*:f)%R) = (`|c|%:E*L (inc f))%E.
    rewrite linearZ; exact: (extended_seminorm_scale hL c (inc f)).
  rewrite -!summable_field_size_exact -EFinM in he.
  by injection he.
- move=> f g.
  have he : (L (inc (f+g)%R) <= L (inc f)+L (inc g))%E.
    rewrite linearD; exact: (extended_seminorm_triangle hL (inc f) (inc g)).
  by rewrite -!summable_field_size_exact -EFinD lee_fin in he.
Qed.
End SummableFieldLaws.
