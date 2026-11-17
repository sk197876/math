(** Federer (1969), 3.4.8(5), p. 328:
    the finite-dimensional analytic germ ring is a
    countable union of compact sets. The original growth
    classes of 3.4.5 give an increasing cover with
    no selected representatives in its public laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP LinearBasis AnalyticGermUP AnalyticGermMetric
  AnalyticGermGrowthUP AnalyticGermGrowthSealed AnalyticGermGrowthCover AnalyticGermGrowthCompact
  IncreasingCompactCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_growth_class_monotone]: the
    original factorial bounds increase with both positive
    integer parameters, supporting the common compact-cover
    index in 3.4.8(5), p. 328. *)
Lemma analytic_germ_growth_class_monotone (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a s t u v:
  (s<=u)%N ->(t<=v)%N ->
  @AnalyticGermGrowth.value R X NX hNX a s t `<=`
    @AnalyticGermGrowth.value R X NX hNX a u v.
Proof.
move=>hS hT alpha hAlpha.
apply/(@analytic_germ_growth_membership R X NX hNX a u v _
  (@AnalyticGermGrowth.laws R X NX hNX a u v) alpha)=>m.
have hOld:=(@analytic_germ_growth_membership R X NX hNX a s t _
  (@AnalyticGermGrowth.laws R X NX hNX a s t) alpha).1 hAlpha m.
have hScalar:(s%:R:R)<=u%:R by rewrite ler_nat.
have hPower:(t%:R^+m:R)<=v%:R^+m.
  have hBase:(t%:R:R)<=v%:R by rewrite ler_nat.
  exact:(lerXn2r m (ler0n R t) (ler0n R v) hBase).
have hProduct:(s%:R*t%:R^+m:R)<=u%:R*v%:R^+m.
  exact:ler_pM (ler0n R s) (exprn_ge0 m (ler0n R t)) hScalar hPower.
exact:le_trans hOld (ler_wpM2r (ler0n R (m`!)) hProduct).
Qed.

(** Source for [analytic_germ_increasing_compact_cover_exists]:
    an actual increasing compact cover of the original
    finite-dimensional germ ring, supporting 3.4.8(5), p. 328.
    The chosen growth-class enumeration remains local; only
    the independent compact-cover laws are exposed. *)
Theorem analytic_germ_increasing_compact_cover_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a n (b:'I_n->X):
  is_basis b ->exists K:nat->set (@analytic_germ_metric R X NX hNX a),
    is_increasing_compact_cover setT K.
Proof.
move=>hb.
pose K i:=@AnalyticGermGrowth.value R X NX hNX a i.+1 i.+1.
exists K;constructor.
- move=>i;exact:(@analytic_germ_growth_class_compact R X NX hNX a n b hb i.+1 i.+1).
- by move=>i alpha hAlpha.
- move=>i j hij;apply:analytic_germ_growth_class_monotone;exact:hij.
- move=>alpha _.
  have [s [t [hS [hT hClass]]]]:=@analytic_germ_positive_growth_cover R X NX hNX a alpha.
  exists (s+t)%N;apply:(@analytic_germ_growth_class_monotone R X NX hNX a
    s t (s+t).+1 (s+t).+1 _ _ alpha hClass).
  + exact:leq_trans (leq_addr t s) (leqnSn (s+t)).
  + exact:leq_trans (leq_addl s t) (leqnSn (s+t)).
Qed.
