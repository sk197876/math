(** Federer (1969), 1.8.1, p. 38: points of the mass unit ball are convex
    combinations of at most binomial(dim V,m) simple unit-ball points, with
    strictly positive coefficients of total one. The printed representation
    requires a nonzero exterior dimension; in dimension zero the hull still
    contains zero but a zero-term sum cannot have total weight one. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP ExteriorGrading AlternatingCoordinates
  LinearBasis FiniteExteriorPowers FiniteOrdinalBasis ExteriorIndices
  SimpleUnitBall ComassUP MassUP MassConvexHull SubconvexCombinations
  SubconvexReduction PositiveCoefficientReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [mass_positive_convex_representation]: Federer 1.8.1,
    p. 38, the convex-combination display and its dimension bound.
    The explicit positive-dimension hypothesis is necessary for the
    printed requirement that the coefficients sum to one. *)
Theorem mass_positive_convex_representation (R : realType)
    (h2 : (1+1 : R) != 0) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (e : 'I_n -> V) (he : is_basis e)
    m (hm : (0 < m)%N) (hdim : (0 < 'C(n,m))%N)
    (kappa : A_m V R^o m -> R)
    (hk : forall phi, is_comass h2 hB phi (kappa phi)) x d :
  is_mass kappa x d -> d <= 1 ->
  exists k, exists u : 'I_k -> exterior_power V m, exists a : 'I_k -> R,
    (k <= 'C(n,m))%N /\ (forall i, simple_unit_ball h2 hB (u i)) /\
    (forall i, 0 < a i) /\ \sum_i a i = 1 /\ x = \sum_i a i *: u i.
Proof.
move=> hd hd1.
have [hx0|hx0] := eqVneq x 0.
- exists 1%N, (fun _ => 0), (fun _ => 1).
  split=> //; split.
  + move=> i; exact: (@simple_unit_ball_zero R h2 V B hB m hm).
  + split; first by move=> i; exact: ltr01.
    split; first by rewrite big_ord_recr big_ord0 /= add0r.
    by rewrite big_ord_recr big_ord0 /= scaler0 add0r hx0.
have hxC := (proj1 (@mass_unit_ball_iff_subconvex R h2 V B hB n e he m hm kappa hk x d hd)) hd1.
case: hxC => j [u [a [hu [ha [hs hx]]]]].
have hb := finite_ordinal_basis (@finite_e_lambda_basis R n V e he h2 m).
have [k [v [b [hkd [hv [hb0 [hbs huv]]]]]]] :=
  @subconvex_dimension_reduction R (exterior_power V m) _ _ hb
    (@simple_unit_ball R h2 V B hB m) j u a hu ha hs.
have [l [w [c [hlk [hw [hc [hcs hcv]]]]]]] :=
  @positive_coefficient_reduction R (exterior_power V m)
    (@simple_unit_ball R h2 V B hB m) k v b hv hb0.
pose t := \sum_i c i.
have ht0 : 0 <= t by apply: sumr_ge0 => i _; exact: ltW (hc i).
have hxt : x = \sum_i c i *: w i by rewrite hx huv -hcv.
have htne : t != 0.
  apply/eqP=> hz; apply: (elimT negP hx0); apply/eqP.
  have hall i : c i = 0.
    have hnon i : 0 <= c i := ltW (hc i).
    exact: (@psumr_eq0P R (Finite.clone 'I_l _) predT c (fun i _ => hnon i) hz i (erefl true)).
  rewrite hxt; apply: big1 => i _; by rewrite hall scale0r.
have htp : 0 < t by rewrite lt0r htne ht0.
have ht1 : t <= 1 by rewrite /t hcs.
exists l, (fun i => t *: w i), (fun i => c i / t).
split; first by rewrite -card_Lambda; exact: leq_trans hlk hkd.
split.
- move=> i; apply: simple_unit_ball_scale hm _ (hw i).
  by rewrite ger0_norm.
split; first by move=> i; exact: divr_gt0 (hc i) htp.
split.
- rewrite -mulr_suml; exact: divff htne.
- rewrite hxt; apply: eq_bigr => i _; by rewrite scalerA divfK.
Qed.

(** Source for [zero_dimensional_positive_convex_impossible]: Federer
    1.8.1, p. 38, local boundary correction to the positive-coefficient
    representation with N <= dim(exterior_m V). If that dimension
    is zero, no such coefficient family can have total one. This is
    a local correction, not an entry in Federer's erratum. *)
Theorem zero_dimensional_positive_convex_impossible (R : fieldType)
    k (a : 'I_k -> R) : (k <= 0)%N -> \sum_i a i != 1.
Proof.
rewrite leqn0 => /eqP hk; move: a; rewrite hk => a.
by rewrite big_ord0 eq_sym oner_eq0.
Qed.
