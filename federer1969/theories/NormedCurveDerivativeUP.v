(** Federer (1969), 2.9.22, pp. 167–168: the derivative of a curve is the
    limit of its difference quotients in the norm topology. This file
    specifies that limit before asserting its existence. The uniqueness and
    elementary cases use only the norm laws, without reflexivity or
    completeness. Chapter 21 has no corresponding reflexive-Banach
    extension. The local Federer erratum has no entry for book pp. 167–168. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals lra.
From Federer Require Import RealNormUP PartialFunctionUP RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [punctured_norm_limit]: supporting norm-topology
    limit in Federer 2.9.22, p. 167, first displayed derivative.
    In words: every positive norm error eventually holds for all
    sufficiently small nonzero real increments, on both sides. *)
Definition punctured_norm_limit (R : realType) (E : lmodType R)
    (N : E -> R) (u : R -> E) (v : E) :=
  forall e : R, 0<e -> exists d : R, 0<d /\
    forall h : R, 0<`|h|<d -> N (u h-v)<e.

(** Source for [punctured_norm_limit_unique]: supporting uniqueness
    of the norm limit g'(x) in Federer 2.9.22, p. 167.
    This follows from the triangle inequality and definiteness;
    no finite-dimensional restriction is imposed. *)
Lemma punctured_norm_limit_unique (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (u : R -> E) (a b : E) :
  punctured_norm_limit N u a -> punctured_norm_limit N u b -> a=b.
Proof.
move=> ha hb; apply: contrapT=> hne.
have hab : 0<N (a-b).
  rewrite (real_norm_positive hN.1 hN.2) subr_eq0; exact/eqP.
pose e := N (a-b)/3.
have he : 0<e by rewrite /e divr_gt0 // ltr0n.
have [da [hda hA]] := ha e he.
have [db [hdb hB]] := hb e he.
pose h := Num.min da db/2.
have hm : 0<Num.min da db by rewrite lt_min hda hdb.
have hh : 0<h by rewrite /h divr_gt0 // ltr0n.
have hsmall : h<Num.min da db by rewrite /h; lra.
have hma : Num.min da db<=da by rewrite ge_min lexx.
have hmb : Num.min da db<=db by rewrite ge_min lexx orbT.
have hnorm : `|h|=h := ger0_norm (ltW hh).
have hha : 0<`|h|<da.
  rewrite hnorm; apply/andP; split; first exact hh.
  exact (lt_le_trans hsmall hma).
have hhb : 0<`|h|<db.
  rewrite hnorm; apply/andP; split; first exact hh.
  exact (lt_le_trans hsmall hmb).
have hAa : N (a-u h)<e.
  rewrite (real_seminorm_subtract hN.1); exact: hA h hha.
have hBb := hB h hhb.
have hid : a-b=(a-u h)+(u h-b) by rewrite addrA subrK.
have hbound := le_lt_trans (real_seminorm_triangle hN.1 (a-u h) (u h-b))
  (ltrD hAa hBb).
rewrite -hid in hbound.
have hback : e+e<=N (a-b) by rewrite /e; lra.
by have hbad := lt_le_trans hbound hback; rewrite ltxx in hbad.
Qed.

(** Source for [has_normed_curve_derivative]: direct norm derivative
    in Federer 2.9.22, p. 167: the quotients (g(x+h)-g(x))/h
    converge to v in Y. Division of a vector means scalar
    multiplication by the inverse real increment. *)
Definition has_normed_curve_derivative (R : realType) (E : lmodType R)
    (N : E -> R) (g : R -> E) (x : R) (v : E) :=
  punctured_norm_limit N (fun h => h^-1 *: (g (x+h)-g x)) v.

(** Source for [normed_curve_derivative]: exact partial derivative
    g' of Federer 2.9.22, p. 167. Its graph contains precisely
    the norm limits, and the norm laws prove single-valuedness;
    no default value is assigned outside its domain. *)
Definition normed_curve_derivative (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> E) : partial_function R E.
Proof.
refine (@Build_partial_function R E (has_normed_curve_derivative N g) _).
move=> x y z; exact: (punctured_norm_limit_unique hN).
Defined.

(** Source for [normed_curve_derivative_graph]: exact graph law
    for the norm derivative in Federer 2.9.22, p. 167;
    supporting specification, without an existence assertion. *)
Lemma normed_curve_derivative_graph (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> E) x v :
  partial_function_graph (normed_curve_derivative hN g) x v <->
  has_normed_curve_derivative N g x v.
Proof. by []. Qed.

(** Source for [constant_normed_curve_derivative]: supporting
    constant-curve case of Federer 2.9.22, p. 167. The result
    includes the zero-dimensional normed space. *)
Lemma constant_normed_curve_derivative (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (c : E) (x : R) :
  has_normed_curve_derivative N (fun _ => c) x 0.
Proof.
move=> e he; exists 1; split; first exact: ltr01.
by move=> h _; rewrite subrr scaler0 subrr (real_seminorm_zero hN.1).
Qed.

(** Source for [scalar_normed_curve_derivative]: compatibility of
    Federer 2.9.22, p. 167, with the real derivative of 2.9.19,
    p. 163. This is equality of the actual two-sided limit
    conditions, rather than an almost-everywhere identification. *)
Lemma scalar_normed_curve_derivative (R : realType) (g : R -> R) x v :
  @has_normed_curve_derivative R R^o (fun y => `|y|) g x v <->
  has_real_curve_derivative g x v.
Proof.
have hq : (fun h : R => h^-1 *: ((g (x+h)-g x) : R^o)) =
    (fun h : R => (g (x+h)-g x)/h).
  apply/funext=> h; change (h^-1 * (g (x+h)-g x) = (g (x+h)-g x)/h).
  by rewrite mulrC.
by rewrite /has_normed_curve_derivative /has_real_curve_derivative hq.
Qed.
