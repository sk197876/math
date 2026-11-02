(** Federer (1969), 1.10.5, p. 47: the exact identity ||phi^m||=m!||phi||^m
    for a one-form with values in a normed associative algebra whose powers
    preserve lengths. We use explicit right-associated positive powers, so
    the result also applies without associativity if those powers satisfy
    the same norm law. No unit is required. Operator norms may be infinite. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal.
From Federer Require Import TensorUP Bilinear NonemptyProduct RealNormUP
  SymmetricForms SymmetricFormWords SymmetricOneFormPowers
  SymmetricOperatorNormUP SymmetricOperatorNorm ExtendedSupremumPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Norm.
Variable R : realType.
Variables V W : lmodType R.
Variables (NV : V -> R) (NW : W -> R).
Hypothesis hV : is_real_seminorm NV.
Hypothesis hW : is_real_seminorm NW.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Hypothesis hsub : forall x y, NW (mu x y)<=NW x*NW y.
Variable f : S_m V W 1.
Variable m : nat.
Hypothesis hm : (0<m)%N.
Local Notation kappa := (symmetric_operator_norm hV NW).
Local Notation power := (symmetric_one_form_power hmu f m).

(** Source for [symmetric_one_form_power_norm_upper]: Federer
    1.10.5, p. 47, the upper estimate for the norm of a
    positive power, including the case of an infinite operator norm. *)
Theorem symmetric_one_form_power_norm_upper :
  (kappa power <= ((m`!)%:R:R)%:E * (kappa f)^+m)%E.
Proof.
have hk0 := symmetric_operator_norm_ge_zero hV hW f.
have hp : 0<((m`!)%:R:R) by rewrite ltr0n fact_gt0.
case he : (kappa f)=> [c| |] in hk0 *.
- rewrite -EFin_expe -EFinM.
  apply: (proj2 (symmetric_operator_norm_bound hV NW power _))=> t ht.
  rewrite lee_fin in hk0.
  apply: (symmetric_one_form_power_finite_bound hW hmu hsub hm hk0)=> i.
  apply: (proj1 (symmetric_operator_norm_bound hV NW f c)); first by rewrite he.
  move=> j; rewrite ord1 tnth0; exact: ht.
- have hy : ((+oo : \bar R)^+m=+oo)%E.
    case: m hm=> [|k] // _.
    elim: k=> [|k ih]; first by rewrite expeS expe0 mule1.
    by rewrite expeS ih mulyy.
  have hpE : (0<((m`!)%:R:R)%:E)%E by rewrite lte_fin.
  by rewrite hy muleC (gt0_mulye hpE) leey.
- by rewrite leeNy_eq in hk0.
Qed.

Hypothesis hpow : forall w, NW (nonempty_product mu 0 (nseq m w))=(NW w)^+m.

(** Source for [symmetric_one_form_power_norm_lower]: Federer
    1.10.5, p. 47, the lower estimate for the power identity.
    Diagonal unit tuples give m! times the powers of one-form values;
    the local supremum-of-powers lemma retains the unbounded case. *)
Theorem symmetric_one_form_power_norm_lower :
  (((m`!)%:R:R)%:E * (kappa f)^+m <= kappa power)%E.
Proof.
have hp : 0<((m`!)%:R:R) by rewrite ltr0n fact_gt0.
rewrite -(lee_pdivlMl _ _ hp).
apply: (@extended_supremum_power_least R (symmetric_form_unit_values NV NW f)
  (kappa f) (symmetric_operator_normP hV NW f)
  (symmetric_form_unit_values_nonempty NW hV f) _ m hm).
- move=> r [t [ht ->]]; exact: real_seminorm_nonnegative hW _.
- move=> r [t [ht ->]].
  have htE : t=[tuple tnth t ord0].
    apply: eq_from_tnth=> i; by rewrite ord1 tnth0.
  have hd : symmetric_form_unit_tuple NV [tuple tnth t ord0 | i<m].
    move=> i; rewrite tnth_mktuple; exact: ht.
  have hh := symmetric_operator_norm_upper hV NW power hd.
  rewrite (symmetric_one_form_power_diagonal hmu f hm)
    (real_seminorm_scale hW) normr_nat hpow in hh.
  rewrite htE (lee_pdivlMl _ _ hp).
  by rewrite -EFinM.
Qed.

(** Source for [symmetric_one_form_power_norm]: Federer 1.10.5,
    p. 47, the displayed equality ||phi^m||=m!||phi||^m.
    The hypotheses are explicit seminorm submultiplicativity and the
    m-th-power norm law; the normed associative case in the book is
    included without assuming finite dimension or boundedness. *)
Theorem symmetric_one_form_power_norm :
  (kappa power = ((m`!)%:R:R)%:E * (kappa f)^+m)%E.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- exact: symmetric_one_form_power_norm_upper.
- exact: symmetric_one_form_power_norm_lower.
Qed.
End Norm.
