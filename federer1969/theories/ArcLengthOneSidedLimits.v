(** Federer (1969), 2.5.16, p. 109: "For each x in R, s(x-) <= s(x) <=
    s(x+), where s(x-) = sup {s(t) : t < x} = lim_(t -> x-) s(t), s(x+) =
    inf {s(t) : t > x} = lim_(t -> x+) s(t)." CurveArcLength.v defines s(x-)
    and s(x+) by the supremum and the infimum; here the second equalities
    are proved, with the one sided filters x^'- and x^'+ of the analysis
    library, as already used for g(x-) and g(x+) in CurveOneSidedLimits.v.
    The proof combines the approximation of the supremum and the infimum
    with the monotonicity of s. The local erratum has no entry for p. 109. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import CurveVariationUP CurveArcLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ArcLengthLimits.
Variable R : realType.
Variable Y : metricType R.
Variable g : R -> Y.
Hypothesis hfin : curve_locally_finite_variation g.
Local Notation s := (arc_length g).
Local Notation sl := (arc_length_left g).
Local Notation sr := (arc_length_right g).

(** Source for [arc_length_left_limit]: s(x-) = lim_(t -> x-) s(t),
    Federer 2.5.16, p. 109, where s(x-) is the supremum
    sup {s(t) : t < x} of CurveArcLength.v. *)
Theorem arc_length_left_limit (x : R) : s @ x^'- --> sl x.
Proof.
apply/cvgrPdist_lt=> e he.
have [t0 ht0x ht0] := arc_length_left_adherent hfin x he.
near=> t.
have htx : t < x by near: t; exact: nbhs_left_lt.
have ht0t : t0 <= t by near: t; exact: (nbhs_left_ge ht0x).
have hle := arc_length_le_left hfin htx.
have hge := arc_length_monotone hfin ht0t.
rewrite ger0_norm ?subr_ge0 //.
by rewrite ltrBlDr addrC -ltrBlDr; exact: lt_le_trans ht0 hge.
Unshelve. all: end_near.
Qed.

(** Source for [arc_length_right_limit]: s(x+) = lim_(t -> x+) s(t),
    Federer 2.5.16, p. 109, where s(x+) is the infimum
    inf {s(t) : t > x} of CurveArcLength.v. *)
Theorem arc_length_right_limit (x : R) : s @ x^'+ --> sr x.
Proof.
apply/cvgrPdist_lt=> e he.
have [t0 hxt0 ht0] := arc_length_right_adherent hfin x he.
near=> t.
have hxt : x < t by near: t; exact: nbhs_right_gt.
have htt0 : t <= t0 by near: t; exact: (nbhs_right_le hxt0).
have hge := arc_length_right_le hfin hxt.
have hle := arc_length_monotone hfin htt0.
rewrite ler0_norm ?subr_le0 // opprB.
by rewrite ltrBlDl; exact: le_lt_trans hle ht0.
Unshelve. all: end_near.
Qed.

(** Source for [arc_length_one_sided_limits]: the complete display
    of Federer 2.5.16, p. 109: s(x-) <= s(x) <= s(x+), with
    s(x-) = sup {s(t) : t < x} = lim_(t -> x-) s(t) and
    s(x+) = inf {s(t) : t > x} = lim_(t -> x+) s(t). The supremum and
    infimum are the defining formulas of [arc_length_left] and
    [arc_length_right]. *)
Theorem arc_length_one_sided_limits (x : R) :
  [/\ sl x <= s x, s x <= sr x, s @ x^'- --> sl x & s @ x^'+ --> sr x].
Proof.
split.
- exact: arc_length_left_le hfin x.
- exact: arc_length_right_ge hfin x.
- exact: arc_length_left_limit.
- exact: arc_length_right_limit.
Qed.

End ArcLengthLimits.
