(** Federer (1969), 1.10.5, pp. 47-48: arbitrary normed input and
    coefficient spaces. The supporting seminorm and norm laws are stated in
    Federer 2.4.12, p. 86; only finite-valued seminorms are specified here.
    These predicates impose laws on a supplied function rather than
    constructing a norm from coordinates or an inner product. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_real_seminorm]: Federer 1.10.5, pp. 47-48,
    normed-space hypotheses, with the finite-valued case of the explicit
    seminorm definition in 2.4.12, p. 86. In words: nonnegativity,
    absolute homogeneity and the triangle inequality. *)
Record is_real_seminorm (R : realFieldType) (V : lmodType R) (N : V -> R) : Prop := {
  real_seminorm_nonnegative : forall x, 0 <= N x;
  real_seminorm_scale : forall a x, N (a *: x) = `|a| * N x;
  real_seminorm_triangle : forall x y, N (x+y) <= N x + N y
}.

(** Source for [is_real_norm]: Federer 1.10.5, pp. 47-48,
    the arbitrary norm hypotheses. As specified in 2.4.12, p. 86,
    a finite-valued seminorm is a norm when only zero has value zero. *)
Definition is_real_norm (R : realFieldType) (V : lmodType R) (N : V -> R) : Prop :=
  is_real_seminorm N /\ forall x, N x = 0 -> x=0.

Section Laws.
Variable R : realFieldType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.

(** Source for [real_seminorm_zero]: Federer 1.10.5,
    pp. 47-48, supporting consequence of the norm laws:
    the value at zero vanishes, even for a seminorm. *)
Lemma real_seminorm_zero : N 0=0.
Proof.
have h := real_seminorm_scale hN 0 (0 : V).
by move: h; rewrite scale0r normr0 mul0r.
Qed.

(** Source for [real_seminorm_negate]: Federer 1.10.5,
    pp. 47-48, supporting symmetry of a seminorm under negation. *)
Lemma real_seminorm_negate x : N (-x)=N x.
Proof. by rewrite -scaleN1r (real_seminorm_scale hN) normrN normr1 mul1r. Qed.

(** Source for [real_seminorm_subtract]: Federer 1.10.5,
    pp. 47-48, supporting symmetry of the distance associated
    with the given norm. *)
Lemma real_seminorm_subtract x y : N (x-y)=N (y-x).
Proof. by rewrite -opprB real_seminorm_negate. Qed.

(** Source for [real_seminorm_sum]: Federer 1.10.5,
    p. 48, supporting triangle inequality for finite decompositions
    into products of vectors. *)
Lemma real_seminorm_sum (I : finType) (x : I -> V) :
  N (\sum_i x i) <= \sum_i N (x i).
Proof.
elim/big_ind2: _=> [|a b c d ha hb|i _].
- by rewrite real_seminorm_zero.
- apply: le_trans (real_seminorm_triangle hN _ _) _.
  exact: lerD ha hb.
- exact: lexx.
Qed.

(** Source for [real_norm_zero_test]: Federer 1.10.5,
    p. 48, positive definiteness required of a norm:
    its value vanishes exactly on the zero vector. *)
Lemma real_norm_zero_test (hd : forall x, N x=0 -> x=0) x :
  (N x == 0) = (x == 0).
Proof.
apply/eqP/eqP=> [hx|->]; first exact: hd.
exact: real_seminorm_zero.
Qed.

(** Source for [real_norm_positive]: Federer 1.10.5,
    pp. 47-48, a norm is strictly positive on every nonzero vector. *)
Lemma real_norm_positive (hd : forall x, N x=0 -> x=0) x :
  (0<N x) = (x!=0).
Proof. by rewrite lt_def (real_norm_zero_test hd) (real_seminorm_nonnegative hN) andbT. Qed.
End Laws.

(** Source for [scalar_absolute_value_norm]: Federer 1.10.5,
    pp. 47-48, the scalar coefficient space and degree-zero norm.
    The usual absolute value satisfies the abstract norm specification. *)
Lemma scalar_absolute_value_norm (R : realFieldType) : @is_real_norm R R^o (fun x : R => `|x|).
Proof.
split.
- split.
  + exact: normr_ge0.
  + by move=> a x; change (`|a*x| = `|a|*`|x|); rewrite normrM.
  + exact: ler_normD.
- move=> x /eqP; by rewrite normr_eq0=> /eqP.
Qed.
