(** Federer (1969), 3.3.19, p. 305: uniform actual
    original-cap mass comparison, with every original parent,
    orientation, half-angle and sufficiently late level retained. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric
  FactorialDiscScalesSealed CircularTrigonometryUP CircularTrigonometrySealed
  RealTrigonometryUP CircularCosineUniformGap CircularDiscNormalizedCapBounds
  NaturalScaledReciprocalTail CircularDiscCaps CircularDiscTreeUP CircularDiscLimitUP HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Uniform.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_uniform_cap_mass]: the exact
    H1(A intersect S(z,r,u,gamma))/(2r) tends to gamma/pi,
    uniformly in all original parents, unit orientations and
    0<=gamma<=pi, as asserted in 3.3.19, p. 305.
    Proved angular counts and a positive uniform cosine gap
    supply the cutoff; no regularity modulus is assumed. *)
Theorem circular_disc_uniform_cap_mass (d:R):0<d ->exists J:nat,
  forall j (z u:E) (gamma:R),(J<=j)%N ->z \in H j ->
  inner_norm (@euclidean_inner_productP R 2) u= 1 ->0<=gamma ->gamma<=p ->
  (((gamma/p-d)%:E<mu (A `&` circular_disc_cap z (rho j) u gamma)/(2* rho j)%:E)%E /\
   (mu (A `&` circular_disc_cap z (rho j) u gamma)/(2* rho j)%:E<(gamma/p+d)%:E)%E).
Proof.
move=>hd.
have hp:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
pose e:= Num.min (p/2) (p* d/4).
have hHalf:0<p/2 by lra.
have hProduct:0<p* d/4 by rewrite divr_gt0 // mulr_gt0.
have he:0<e by rewrite /e lt_min hHalf hProduct.
have heHalf:e<=p/2 by rewrite /e ge_min lexx.
have heProduct:e<=p* d/4 by rewrite /e ge_min lexx orbT.
have hep:e<p by lra.
have heBudget:e/p<=d/4.
  rewrite ler_pdivrMr //;nra.
have hGap:0<2*(S (e/2))^+2.
  have hZero:0<= (0:R) by exact:lexx.
  have hLast:(0:R)<=p-e by lra.
  exact:(@circular_cosine_uniform_gap R e 0 he hep hZero hLast).1.
have hTwo:0<(2:R) by rewrite ltr0n.
have hOne:0<(1:R) by exact:ltr01.
have hQuarter:0<d/4 by lra.
have [J1 hJ1]:= @natural_scaled_reciprocal_tail R 2 (2*(S (e/2))^+2) hTwo hGap.
have [J2 hJ2]:= @natural_scaled_reciprocal_tail R 1 (d/4) hOne hQuarter.
exists (maxn J1 J2)=>j z u gamma hj hz hu hGamma hGammaP.
have hj1:(J1<=j+4)%N:= leq_trans (leq_trans (leq_maxl J1 J2) hj) (leq_addr 4 j).
have hj2:(J2<=j+4)%N:= leq_trans (leq_trans (leq_maxr J1 J2) hj) (leq_addr 4 j).
have [_ hSmall]:= hJ1 _ hj1.
have [_ hReciprocal]:= hJ2 _ hj2.
have [hLower hUpper]:= @circular_disc_normalized_cap_bounds R H hH A hA j z u e gamma
  hz hu he hep hGamma hGammaP hSmall.
have hStrictLower:gamma/p-d<gamma/p-e/p-1/(j+4)%:R by lra.
have hStrictUpper:gamma/p+e/p+1/(j+4)%:R<gamma/p+d by lra.
split.
- exact:(lt_le_trans (lte_tofin hStrictLower) hLower).
- exact:(le_lt_trans hUpper (lte_tofin hStrictUpper)).
Qed.
End Uniform.
