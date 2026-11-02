(** Federer (1969), 1.10.5, p. 48: public polynomial norm, exposed through
    its abstract supremum laws. Source context and the extended-valued
    convention: PolynomialNormUP.v. Existence comes from the sealed
    order-theoretic supremum interface. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal.
From Federer Require Import RealNormUP ExtendedSupremumUP ExtendedSupremumSealed PolynomialNormUP.
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

(** Source for [polynomial_norm]: Federer 1.10.5,
    p. 48, the supremum of output lengths on the input unit
    ball. This interface does not require a coordinate representation. *)
Definition polynomial_norm (P : V -> W) : \bar R :=
  @ExtendedSupremum.value R (polynomial_unit_values NV NW P)
    (polynomial_unit_values_nonempty NW hV P).

(** Source for [polynomial_normP]: Federer 1.10.5,
    p. 48, the public norm satisfies the abstract supremum laws. *)
Lemma polynomial_normP (P : V -> W) : is_polynomial_norm NV NW P (polynomial_norm P).
Proof. exact: ExtendedSupremum.laws. Qed.

(** Source for [polynomial_norm_upper]: Federer 1.10.5,
    p. 48, every evaluation in the unit ball is bounded
    by the polynomial norm. *)
Lemma polynomial_norm_upper (P : V -> W) x : NV x<=1 ->
  ((NW (P x))%:E <= polynomial_norm P)%E.
Proof.
move=> hx; apply: (@extended_supremum_upper R _ _ (polynomial_normP P)).
by exists x.
Qed.

(** Source for [polynomial_norm_least]: Federer 1.10.5,
    p. 48, every extended upper bound on unit-ball evaluations
    bounds the public norm. *)
Lemma polynomial_norm_least (P : V -> W) c :
  (forall x, NV x<=1 -> ((NW (P x))%:E<=c)%E) -> (polynomial_norm P<=c)%E.
Proof.
move=> hc; apply: (@extended_supremum_least R _ _ (polynomial_normP P)).
move=> r [x [hx ->]]; exact: hc hx.
Qed.

(** Source for [polynomial_norm_bound]: Federer 1.10.5,
    p. 48, a finite bound on the polynomial norm is equivalent
    to the same bound on every unit-ball evaluation. *)
Lemma polynomial_norm_bound (P : V -> W) L :
  (polynomial_norm P <= L%:E)%E <-> forall x, NV x<=1 -> NW (P x)<=L.
Proof.
split.
- move=> hL x hx; have hh := le_trans (polynomial_norm_upper P hx) hL.
  by rewrite lee_fin in hh.
- move=> hb; apply: polynomial_norm_least=> x hx; rewrite lee_fin; exact: hb.
Qed.

(** Source for [polynomial_norm_nonnegative]: Federer 1.10.5,
    p. 48, the polynomial norm is nonnegative, including
    the unbounded case. *)
Lemma polynomial_norm_nonnegative (hW : is_real_seminorm NW) (P : V -> W) :
  (0<=polynomial_norm P)%E.
Proof.
apply: (@extended_supremum_nonnegative R _ _ (polynomial_normP P)).
exists (NW (P 0)); split; last exact: real_seminorm_nonnegative hW (P 0).
exists 0; split=> //; by rewrite (real_seminorm_zero hV) ler01.
Qed.
End Interface.
