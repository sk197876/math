(** Federer (1969), 1.7.6, pp. 33-34: elementary consequences of the
    operator norm formula, supporting the exterior-power estimates and
    positivity criteria. These consequences use only the abstract norm
    specification. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Laws.
Variable R : rcfType.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable f : {linear V -> U}.
Variable L : R.
Hypothesis hL : is_operator_norm hB hC f L.

(** Source for [operator_norm_le_unit]: Federer 1.7.6, p. 33,
    supporting least-upper-bound property on the unit ball. *)
Lemma operator_norm_le_unit M : L <= M <->
  forall x, inner_norm hB x <= 1 -> inner_norm hC (f x) <= M.
Proof.
split.
- move=> h x hx; apply: le_trans _ h.
  exact: (@operator_norm_unit_bound R V U B C hB hC f L hL x hx).
- move=> h; have [x [hx <-]] := operator_norm_attained hL; exact: h x hx.
Qed.

(** Source for [operator_norm_zero_iff]: Federer 1.7.6,
    pp. 33-34, supporting definiteness: zero operator norm
    is equivalent to the map vanishing on every vector. *)
Theorem operator_norm_zero_iff : L = 0 <-> forall x, f x = 0.
Proof.
split.
- move=> h x.
  have hh := @operator_norm_vector_bound R V U B C hB hC f L hL x.
  rewrite h mul0r in hh.
  have hn : inner_norm hC (f x) = 0.
    apply/eqP; rewrite eq_le; apply/andP; split=> //; exact: inner_norm_nonnegative.
  apply/eqP; by rewrite -(inner_norm_eq0 hC) hn eqxx.
- move=> h; have [x [_ <-]] := operator_norm_attained hL.
  by rewrite h inner_norm0.
Qed.

(** Source for [operator_norm_positive_iff]: Federer 1.7.6,
    p. 34, supporting positivity criterion: the norm is positive
    exactly when the linear map is nonzero. *)
Theorem operator_norm_positive_iff : 0 < L <-> exists x, f x != 0.
Proof.
split.
- move=> hp.
  have [x [_ hx]] := operator_norm_attained hL.
  exists x; apply/eqP=> hz.
  by rewrite hz inner_norm0 in hx; rewrite -hx ltxx in hp.
- move=> [x hx].
  rewrite lt_def; apply/andP; split.
  + apply/eqP=> hz; have hh := proj1 operator_norm_zero_iff hz x.
    by rewrite hh eqxx in hx.
  + exact: operator_norm_nonnegative hL.
Qed.
End Laws.
