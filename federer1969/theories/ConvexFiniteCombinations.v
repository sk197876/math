(** Federer (1969), 1.8.1, p. 38: the convex hull consists of finite convex
    combinations. This supporting induction proves closure under finite
    combinations directly from the segment definition of convexity; unused
    total weight is assigned to zero. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import InnerConvex SubconvexCombinations ConvexHullUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Closure.
Variable R : realFieldType.
Variable V : lmodType R.
Variable C : set V.
Hypothesis hC : is_inner_convex C.
Hypothesis h0 : C 0.

(** Source for [convex_subconvex_sum]: Federer 1.8.1,
    p. 38, supporting closure of a convex set containing zero under
    nonnegative finite combinations whose weights sum to at most one. *)
Theorem convex_subconvex_sum n (u : 'I_n -> V) (a : 'I_n -> R) :
  (forall i, C (u i)) -> (forall i, 0 <= a i) -> \sum_i a i <= 1 ->
  C (\sum_i a i *: u i).
Proof.
elim: n u a => [|n ih] u a hu ha hsum; first by rewrite big_ord0.
pose v (i : 'I_n) := u (widen_ord (leqnSn n) i).
pose b (i : 'I_n) := a (widen_ord (leqnSn n) i).
pose r := a ord_max.
have hb i : 0 <= b i := ha (widen_ord (leqnSn n) i).
have hr0 : 0 <= r := ha ord_max.
have hs0 : 0 <= \sum_i b i by apply: sumr_ge0 => i _; exact: hb.
have hs : (\sum_i b i)+r <= 1.
  by rewrite big_ord_recr in hsum.
have hr1 : r <= 1.
  apply: (le_trans _ hs); by rewrite lerDr.
have hvalue : (\sum_i a i *: u i) = (\sum_i b i *: v i)+r *: u ord_max.
  by rewrite big_ord_recr.
rewrite hvalue.
have [hr|hr] := eqVneq r 1.
- have hbs : \sum_i b i = 0.
    apply/eqP; rewrite eq_le; apply/andP; split=> //.
    by rewrite hr -[leRHS](add0r (1 : R)) lerD2r in hs.
  have hbz i : b i = 0.
    exact (@psumr_eq0P R (Finite.clone 'I_n _) (fun _ => true) b
      (fun i _ => hb i) hbs i isT).
  have hz : \sum_i b i *: v i = 0.
    apply: big1 => i _; by rewrite hbz scale0r.
  by rewrite hz hr scale1r add0r; exact: hu.
have hq : 0 < 1-r by rewrite subr_gt0 lt_neqAle hr hr1.
have hq0 : (1-r) != 0 by rewrite gt_eqF.
pose c i := b i / (1-r).
have hc i : 0 <= c i by rewrite /c divr_ge0 //; exact: ltW hq.
have hcs : \sum_i c i <= 1.
  rewrite /c -mulr_suml (@ler_pdivrMr R (1-r) 1 (\sum_i b i) hq) mul1r lerBrDl.
  by rewrite addrC.
have hz := ih v c (fun i => hu (widen_ord (leqnSn n) i)) hc hcs.
have hh := @hC (\sum_i c i *: v i) (u ord_max) hz (hu ord_max) r hr0 hr1.
have hscale : (1-r) *: (\sum_i c i *: v i) = \sum_i b i *: v i.
  rewrite scaler_sumr; apply: eq_bigr => i _; rewrite scalerA /c.
  congr (_ *: _); by rewrite mulrCA mulfV // mulr1.
by rewrite hscale in hh.
Qed.
End Closure.

(** Source for [subconvex_hull_laws]: Federer 1.8.1,
    p. 38, finite combinations give precisely the convex hull when
    zero belongs to S. This conclusion is stated by its universal laws. *)
Theorem subconvex_hull_laws (R : realFieldType) (V : lmodType R)
    (S : set V) : S 0 -> is_convex_hull S (subconvex_combinations S).
Proof.
move=> h0; constructor.
- move=> x hx; exact: subconvex_combinations_include hx.
- exact: subconvex_combinations_convex.
- move=> D hSD hD x [n [u [a [hu [ha [hs ->]]]]]].
  exact (@convex_subconvex_sum R V D hD (hSD _ h0) n u a
    (fun i => hSD _ (hu i)) ha hs).
Qed.
