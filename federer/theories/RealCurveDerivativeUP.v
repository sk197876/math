(** Federer (1969), 2.9.19, pp. 163–165: the real derivative is the finite
    two-sided limit of the difference quotient at nonzero increments. The
    derivative is a single-valued partial graph, without assigning a value
    at a point where no derivative exists. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals lra.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [punctured_real_limit]: supporting precise two-sided limit
    for Federer 2.9.19, p. 163. The epsilon condition ranges over all
    nonzero increments of sufficiently small absolute value, on both sides
    of zero; no sequence is substituted for that limit. *)
Definition punctured_real_limit (R : realType) (u : R -> R) (l : R) :=
  forall e : R, 0<e -> exists d : R, 0<d /\
    forall h : R, 0<`|h|<d -> `|u h-l|<e.

(** Source for [punctured_real_limit_unique]: supporting uniqueness of the
    finite limit defining g' in Federer 2.9.19, p. 163 A common positive
    increment inside both cutoffs and the triangle inequality force
    equality. *)
Lemma punctured_real_limit_unique (R : realType) (u : R -> R) (a b : R) :
  punctured_real_limit u a -> punctured_real_limit u b -> a=b.
Proof.
move=> ha hb; apply: contrapT=> hne.
have hab : 0<`|a-b|.
  rewrite normr_gt0 subr_eq0; exact/eqP.
pose e := `|a-b|/3.
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
have hAa : `|a-u h|<e by rewrite distrC; exact: hA h hha.
have hBb := hB h hhb.
have hbound := le_lt_trans (ler_distD (u h) a b) (ltrD hAa hBb).
have hback : e+e<=`|a-b| by rewrite /e; lra.
by have hbad := lt_le_trans hbound hback; rewrite ltxx in hbad.
Qed.

(** Source for [punctured_real_constant_limit]: constant- function boundary
    case of the finite limit used in Federer 2.9.19, p. 163 Supporting
    elementary limit law. *)
Lemma punctured_real_constant_limit (R : realType) (c : R) :
  punctured_real_limit (fun _ : R => c) c.
Proof.
move=> e he; exists 1; split; first exact: ltr01.
by move=> h _; rewrite subrr normr0.
Qed.

(** Source for [has_real_curve_derivative]: direct finite derivative formula
    g'(x)=lim_(h->0)(g(x+h)-g(x))/h in Federer 2.9.19, p. 163. This is a
    property of a candidate value, preceding existence assertions for
    functions of locally bounded variation. *)
Definition has_real_curve_derivative (R : realType) (g : R -> R) (x v : R) :=
  punctured_real_limit (fun h => (g (x+h)-g x)/h) v.

(** Source for [real_curve_derivative]: direct partial derivative g' in
    Federer 2.9.19, p. 163 The preceding uniqueness lemma proves the
    function law without choosing values off its domain. *)
Definition real_curve_derivative (R : realType) (g : R -> R) : partial_function R R.
Proof.
refine (@Build_partial_function R R (has_real_curve_derivative g) _).
move=> x y z; exact: punctured_real_limit_unique.
Defined.

(** Source for [real_curve_derivative_graph]: direct graph specification of
    g' in Federer 2.9.19, p. 163 A point has derivative v exactly when its
    actual difference quotient has the finite punctured two-sided limit v. *)
Lemma real_curve_derivative_graph (R : realType) (g : R -> R) x v :
  partial_function_graph (real_curve_derivative g) x v <-> has_real_curve_derivative g x v.
Proof. by []. Qed.
