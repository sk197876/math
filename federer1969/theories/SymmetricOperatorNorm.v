(** Federer (1969), 1.10.5, p. 47: public operator norm of a symmetric form.
    Source context and hypotheses: SymmetricOperatorNormUP.v. Existence is
    supplied by the sealed least-upper-bound interface; no coordinates or
    boundedness choices are exposed to downstream proofs. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal.
From Federer Require Import RealNormUP SymmetricForms ExtendedSupremumUP
  ExtendedSupremumSealed SymmetricOperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Interface.
Variable R : realType.
Variables V W : lmodType R.
Variable NV : V -> R.
Hypothesis hV : is_real_seminorm NV.
Variable NW : W -> R.

(** Source for [symmetric_operator_norm]: Federer 1.10.5,
    p. 47, the form-norm supremum over tuples of unit-ball vectors,
    including possibly unbounded forms and degree-zero forms. *)
Definition symmetric_operator_norm m (f : S_m V W m) : \bar R :=
  @ExtendedSupremum.value R (symmetric_form_unit_values NV NW f)
    (symmetric_form_unit_values_nonempty NW hV f).

(** Source for [symmetric_operator_normP]: Federer 1.10.5,
    p. 47, the public norm satisfies its abstract supremum specification. *)
Lemma symmetric_operator_normP m (f : S_m V W m) :
  is_symmetric_operator_norm NV NW f (symmetric_operator_norm f).
Proof. exact: ExtendedSupremum.laws. Qed.

(** Source for [symmetric_operator_norm_upper]: Federer 1.10.5,
    p. 47, each unit-tuple evaluation is bounded by the public norm. *)
Lemma symmetric_operator_norm_upper m (f : S_m V W m) t :
  symmetric_form_unit_tuple NV t -> ((NW (f t))%:E <= symmetric_operator_norm f)%E.
Proof. exact (@symmetric_operator_norm_unit_bound R V W NV NW m f
  (symmetric_operator_norm f) (symmetric_operator_normP f) t). Qed.

(** Source for [symmetric_operator_norm_least]: Federer 1.10.5,
    p. 47, the norm is below every extended upper bound of its
    unit-tuple values, including infinite bounds. *)
Lemma symmetric_operator_norm_least m (f : S_m V W m) c :
  (forall t, symmetric_form_unit_tuple NV t -> ((NW (f t))%:E <= c)%E) ->
  (symmetric_operator_norm f <= c)%E.
Proof.
move=> h; apply: (@extended_supremum_least R _ _ (symmetric_operator_normP f)).
move=> r [t [ht ->]]; exact: h ht.
Qed.

(** Source for [symmetric_operator_norm_bound]: Federer 1.10.5,
    p. 47, finite bounds can be proved directly on unit-tuple evaluations. *)
Lemma symmetric_operator_norm_bound m (f : S_m V W m) L :
  (symmetric_operator_norm f <= L%:E)%E <->
    forall t, symmetric_form_unit_tuple NV t -> NW (f t) <= L.
Proof. exact (@symmetric_operator_norm_le_finite R V W NV NW m f
  (symmetric_operator_norm f) (symmetric_operator_normP f) L). Qed.

(** Source for [symmetric_operator_norm_ge_zero]: Federer 1.10.5,
    p. 47, the public norm is a nonnegative extended real when
    the output function is a seminorm. *)
Lemma symmetric_operator_norm_ge_zero (hW : is_real_seminorm NW)
    m (f : S_m V W m) : (0 <= symmetric_operator_norm f)%E.
Proof. exact (@symmetric_operator_norm_nonnegative R V W NV NW m hV hW f
  (symmetric_operator_norm f) (symmetric_operator_normP f)). Qed.
End Interface.
