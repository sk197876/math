(** Federer (1969), 2.4.12, p. 86, norming-functional corollary. The
    explicit premise N(v)<infinity repairs the unrestricted printed
    assertion; the counterexample is in ExtendedSeminormNormingCorrection.v
    and is separate from Federer's erratum. The ambient seminorm may still
    be infinite at other vectors. Source context: ExtendedSeminormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedSeminormUP ExtendedSeminormLaws PartialLinearMap ExtendedHahnBanach.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Line.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> \bar R.
Hypothesis hN : is_extended_seminorm N.
Variable v : V.
Hypothesis hv : (N v < +oo)%E.

(** Source for [extended_seminorm_line_graph]: the line map
    t*v to t*N(v) in Federer 2.4.12, p. 86,
    interpreted as real-valued under the necessary finiteness premise. *)
Definition extended_seminorm_line_graph (x : V) (a : R^o) :=
  exists t : R, x=t *: v /\ a=t*fine (N v).

(** Source for [extended_seminorm_line_graph_linear]: legitimacy
    of the line functional in Federer 2.4.12, p. 86,
    including v = 0 and a nontrivial seminorm kernel. *)
Lemma extended_seminorm_line_graph_linear : linear_graph extended_seminorm_line_graph.
Proof.
split; first by exists 0; rewrite scale0r mul0r.
split.
- move=> x y a b [s [-> ->]] [t [-> ->]]; exists (s+t).
  by rewrite scalerDl mulrDl.
split.
- move=> c x a [t [-> ->]]; exists (c*t).
  split; first by rewrite scalerA.
  change (c*(t*fine (N v)) = (c*t)*fine (N v)); exact: mulrA.
- move=> x a b [s [hs ->]] [t [ht ->]].
  case: (eqVneq v 0)=> [hv0|hv0].
  + by rewrite hv0 (extended_seminorm_zero hN) /= !mulr0.
  + have hz : (s-t) *: v = 0 by rewrite scalerBl -hs -ht subrr.
    have hst : s=t.
      move/eqP: hz; by rewrite scaler_eq0 (negPf hv0) orbF subr_eq0=> /eqP.
    by rewrite hst.
Qed.

(** Source for [extended_seminorm_line_graph_dominated]:
    domination of the initial line map in Federer 2.4.12,
    p. 86, using t*N(v)<=|t|*N(v). *)
Lemma extended_seminorm_line_graph_dominated x a :
  extended_seminorm_line_graph x a -> (a%:E <= N x)%E.
Proof.
move=> [t [-> ->]].
have hfin : N v \is a fin_num by rewrite (ge0_fin_numE (extended_seminorm_nonnegative hN v)).
rewrite (extended_seminorm_scale hN) -(fineK hfin) -EFinM lee_fin.
apply: ler_wpM2r; last exact: ler_norm.
have h := extended_seminorm_nonnegative hN v; by rewrite -(fineK hfin) lee_fin in h.
Qed.

(** Source for [extended_seminorm_norming_functional]: corrected
    norming-functional corollary of Federer 2.4.12, p. 86.
    Finiteness is required only at the prescribed vector, and
    the resulting functional is dominated everywhere. *)
Theorem extended_seminorm_norming_functional :
  exists f : {linear V -> R^o}, (forall x, (`|f x|%:E <= N x)%E) /\
    (f v)%:E=N v.
Proof.
have [f [hf hb]] := extended_seminorm_hahn_banach hN
  extended_seminorm_line_graph_linear extended_seminorm_line_graph_dominated.
exists f; split; first exact (@extended_dominated_functional_absolute_bound R V N hN f hb).
have hg : extended_seminorm_line_graph v (fine (N v)) by exists 1; rewrite scale1r mul1r.
rewrite (hf _ _ hg) fineK // (ge0_fin_numE (extended_seminorm_nonnegative hN v)); exact hv.
Qed.
End Line.
