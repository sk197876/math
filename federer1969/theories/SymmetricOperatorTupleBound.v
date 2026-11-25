(** Federer (1969), 1.10.5, p. 47: homogeneous bounds underlying the
    contraction and symmetric-product estimates. The tuple bound below also
    permits an infinite operator norm, with the usual nonnegative
    extended-real convention zero times infinity is zero. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal.
From Federer Require Import RealNormUP RealNormNormalization SymmetricForms
  SymmetricTupleScaling SymmetricOperatorNormUP SymmetricOperatorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section TupleBound.
Variable R : realType.
Variables V W : lmodType R.
Variable NV : V -> R.
Variable NW : W -> R.
Hypothesis hV : is_real_norm NV.
Hypothesis hW : is_real_seminorm NW.
Local Notation hN := (proj1 hV).
Local Notation normalize := (real_norm_normalize NV).

(** Source for [symmetric_form_normalized_value]: Federer 1.10.5,
    p. 47, supporting normalization of all arguments. The output
    norm factors as the product of the input lengths times the output
    norm on normalized arguments. Positive definiteness handles zero factors. *)
Lemma symmetric_form_normalized_value m (f : S_m V W m) (t : m.-tuple V) :
  NW (f t) = (\prod_(i < m) NV (tnth t i)) *
    NW (f [tuple normalize (tnth t i) | i < m]).
Proof.
have he : t = [tuple NV (tnth t i) *: normalize (tnth t i) | i < m].
  apply: eq_from_tnth=> i; rewrite tnth_mktuple.
  symmetry; exact (@real_norm_normalize_reconstruct R V NV (proj2 hV) (tnth t i)).
have hp : 0 <= \prod_(i < m) NV (tnth t i).
  apply: prodr_ge0=> i _; exact: real_seminorm_nonnegative hN (tnth t i).
rewrite {1}he symmetric_form_tuple_scalars (real_seminorm_scale hW).
by rewrite (ger0_norm hp).
Qed.

(** Source for [symmetric_operator_tuple_bound]: Federer 1.10.5,
    p. 47, supporting homogeneous bound: the value on arbitrary
    vectors is bounded by the form norm times their lengths. The statement
    is valid also for unbounded forms and for degree zero. *)
Theorem symmetric_operator_tuple_bound m (f : S_m V W m) (t : m.-tuple V) :
  ((NW (f t))%:E <=
    (\prod_(i < m) NV (tnth t i))%:E * symmetric_operator_norm hN NW f)%E.
Proof.
rewrite symmetric_form_normalized_value EFinM.
apply: lee_wpmul2l.
- rewrite lee_fin; apply: prodr_ge0=> i _; exact: real_seminorm_nonnegative hN (tnth t i).
- apply: symmetric_operator_norm_upper=> i; rewrite tnth_mktuple.
  exact (@real_norm_normalize_unit R V NV hN (tnth t i)).
Qed.

(** Source for [symmetric_operator_finite_tuple_bound]: Federer 1.10.5,
    p. 47, the real-valued form of the homogeneous evaluation bound
    whenever a finite constant L bounds the operator norm. *)
Theorem symmetric_operator_finite_tuple_bound m (f : S_m V W m) L :
  (symmetric_operator_norm hN NW f <= L%:E)%E -> forall (t : m.-tuple V),
  NW (f t) <= L * \prod_(i < m) NV (tnth t i).
Proof.
move=> hL t; rewrite symmetric_form_normalized_value mulrC.
apply: ler_wpM2r.
- apply: prodr_ge0=> i _; exact: real_seminorm_nonnegative hN (tnth t i).
- apply: (proj1 (symmetric_operator_norm_bound hN NW f L) hL)=> i.
  rewrite tnth_mktuple; exact (@real_norm_normalize_unit R V NV hN (tnth t i)).
Qed.
End TupleBound.
