(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    dgpr_blueprint.tex, proofs of lem:heat_extension(1) and lem:classes
    (cl:dt): differentiation under the integral sign, "justified by the mean
    value theorem and Lebesgue's bounded convergence theorem [Federer 2.4.9]".
    Suppose nu is a measure over a set T, X and Z are normed spaces, and
    f : X -> T -> Z. If f(x,y) is differentiable in x near a point a, the
    differentials D_x f(x,y) are bounded by a nu summable function of y
    uniformly for x near a, and the integrals F(x) = int f(x,y) d nu y
    exist in the sense of Federer 2.4.12, then F is differentiable at a with
    DF(a)(v) = int D_x f(a,y)(v) d nu y. Under continuity of D_x f(.,y) the
    map F is of class 1. Neither finite dimension nor completeness of X or Z
    is assumed; the integrals are given by their defining laws. The proof
    follows the blueprint: the mean value inequality bounds the difference
    quotients, and the bounded convergence theorem passes to the limit along
    sequences. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureVectorIntegralUP
  SummableRealFunctionUP SummableRealArithmetic TotalVectorIntegralArithmetic
  TotalVectorIntegralEstimate TotalVectorDominatedLimit NormDifferentialUP NormDifferentialLocal
  NormDifferentialConvexBound InnerConvex NormClassOneUP NormConvexHullDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dgpr_reciprocal_eventually]: supporting Archimedean step
    of the blueprint proof of lem:heat_extension(1): the numbers 1/(m+1)
    are eventually smaller than any positive number. *)
Lemma dgpr_reciprocal_eventually (R : realType) (d : R) :
  0 < d -> exists N : nat, forall m : nat, (N <= m)%N -> (m.+1%:R)^-1 < d.
Proof.
move=> hd.
have hdi : 0 <= d^-1 by rewrite invr_ge0 ltW.
have hb := archi_boundP hdi.
exists (Num.Def.archi_bound d^-1)=> m hm.
have hpos : (0 : R) < m.+1%:R by rewrite ltr0n.
rewrite -(invrK d) ltf_pV2 ?posrE ?invr_gt0 //.
apply: (lt_le_trans hb); rewrite ler_nat; exact: (leq_trans hm (leqnSn m)).
Qed.

Section ParameterIntegral.
Variable R : realType.
Variable T : choiceType.
Variable nu : set T -> \bar R.
Hypothesis hnu : is_measure nu.
Variables X Z : lmodType R.
Variables (NX : X -> R) (NZ : Z -> R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNZ : is_real_norm NZ.

(** Source for [dgpr_has_integral]: the vector integral of Federer 2.4.12,
    pp. 87–88, used in def:heat and lem:heat_extension of the blueprint:
    z = int k d nu for a total map k : T -> Z. This is the public defining
    predicate of Federer's integral, written for total maps. *)
Definition dgpr_has_integral (k : T -> Z) (z : Z) :=
  is_measure_vector_integral nu
    (partial_function_total (fun y => (k y : real_norm_metric_space hNZ))) z.

(** Source for [dgpr_sequence_contradiction]: supporting sequential
    argument in the blueprint proof of lem:heat_extension(1). If no sequence
    h_n with |h_n| < min(r, 1/(n+1)) consists of bad increments, then all
    sufficiently small increments are good. *)
Lemma dgpr_sequence_contradiction (B : X -> Prop) (r : R) :
  0 < r ->
  (forall hs : nat -> X,
    (forall n, NX (hs n) < r /\ NX (hs n) < (n.+1%:R)^-1 /\ B (hs n)) -> False) ->
  exists d : R, 0 < d /\ forall h, NX h < d -> ~ B h.
Proof.
move=> hr hseq; apply: contrapT=> hno.
have hbad n : exists h, NX h < r /\ NX h < (n.+1%:R)^-1 /\ B h.
  apply: contrapT=> hc; apply: hno.
  exists (Num.min r (n.+1%:R)^-1); split.
    by rewrite lt_min hr invr_gt0 ltr0n.
  move=> h hh hB; apply: hc; exists h.
  by move: hh; rewrite lt_min=> /andP [h1 h2].
have [hs hhs] := choice hbad.
exact: (hseq hs hhs).
Qed.

(** Source for [dgpr_integral_zero]: supporting identity int 0 d nu = 0 of
    Federer 2.4.12, p. 87, used in the blueprint proof of
    lem:heat_extension(1). It is obtained from any integrable map. *)
Lemma dgpr_integral_zero (k : T -> Z) (z : Z) :
  dgpr_has_integral k z ->
  dgpr_has_integral (fun y => 0 *: k y) 0.
Proof.
move=> hk; have h := @total_vector_integral_scale R T Z NZ hNZ nu hnu k z 0 hk.
by rewrite scale0r in h.
Qed.

(** Source for [dgpr_parameter_integral_differential]: differentiation
    under the integral sign in the blueprint proof of lem:heat_extension(1),
    "justified by the mean value theorem and Lebesgue's bounded convergence
    theorem [Federer 2.4.9]". Suppose 0 < r, the ball of radius r about a
    lies in A, the maps f(.,y) are differentiable at the points of this ball
    with differentials Df(.,y) bounded by g(y) for a nu summable g, and
    F(x) = int f(x,y) d nu y there. If L(v) = int Df(a,y)(v) d nu y for
    every v, then L = DF(a). *)
Theorem dgpr_parameter_integral_differential (A : set X) (f : X -> T -> Z)
    (Df : X -> T -> Hom X Z) (g : T -> R) (F : X -> Z) (L : Hom X Z) (a : X) (r : R) :
  0 < r -> (forall h, NX h < r -> A (a+h)) ->
  (forall h, NX h < r -> dgpr_has_integral (f (a+h)) (F (a+h))) ->
  (forall v, dgpr_has_integral (fun y => Df a y v) (L v)) ->
  (forall h y, NX h < r ->
    has_norm_differential NX NZ A (fun x => f x y) (a+h) (Df (a+h) y)) ->
  summable_real_functions nu g ->
  (forall h y v, NX h < r -> NZ (Df (a+h) y v) <= g y * NX v) ->
  has_norm_differential NX NZ A F a L.
Proof.
move=> hr hA hF hL hD [b hb] hbound.
have hNX0 : NX 0 = 0 := real_seminorm_zero hNX.1.
have h0 : NX 0 < r by rewrite hNX0.
have hFa : dgpr_has_integral (f a) (F a).
  by have := hF 0 h0; rewrite addr0.
have hDa y : has_norm_differential NX NZ A (fun x => f x y) a (Df a y).
  by have := hD 0 y h0; rewrite addr0.
have hba y v : NZ (Df a y v) <= g y * NX v.
  by have := hbound 0 y v h0; rewrite addr0.
have hgpos y h : 0 < NX h -> 0 <= g y.
  move=> hh; have := hba y h.
  have := real_seminorm_nonnegative hNZ.1 (Df a y h)=> h1 h2.
  by rewrite -(pmulr_lge0 _ hh); exact: le_trans h1 h2.
have hgg : summable_real_functions nu (fun y => g y + g y).
  by apply: (@summable_real_add R T nu hnu g g); exists b.
split.
- by exists r; split.
- exists `|b|; split; first exact: normr_ge0.
  move=> v.
  have hI := @real_total_integral_scale R T nu hnu g b (NX v) hb.
  have hdomv y : NZ (Df a y v) <= NX v * g y by rewrite mulrC; exact: hba.
  have hle := @total_vector_integral_dominated_norm R T Z NZ hNZ nu hnu
    (fun y => Df a y v) (L v) (fun y => NX v * g y) (NX v * b) (hL v) hI hdomv.
  apply: (le_trans hle); rewrite mulrC.
  exact: (ler_wpM2r (real_seminorm_nonnegative hNX.1 v) (ler_norm b)).
- move=> e he.
  pose B h := A (a+h) /\ e * NX h < NZ (F (a+h)-F a-L h).
  have hc : exists d : R, 0 < d /\ forall h, NX h < d -> ~ B h.
    apply: (dgpr_sequence_contradiction hr)=> hs hhs.
    have hpos n : 0 < NX (hs n).
      rewrite (real_norm_positive hNX.1 hNX.2); apply/negP=> /eqP h0n.
      have [_ [_ [_ hlt]]] := hhs n; move: hlt.
      rewrite h0n addr0 subrr linear0 subr0 (real_seminorm_zero hNZ.1) hNX0 mulr0.
      by rewrite ltxx.
    pose c n := (NX (hs n))^-1.
    have hcpos n : 0 < c n by rewrite /c invr_gt0.
    have hcancel n (t : R) : c n * (t * NX (hs n)) = t.
      by rewrite /c mulrCA mulVf ?mulr1 //; exact: lt0r_neq0 (hpos n).
    pose q n y := c n *: (f (a+hs n) y-f a y-Df a y (hs n)).
    pose s n := c n *: (F (a+hs n)-F a-L (hs n)).
    have hq n : dgpr_has_integral (q n) (s n).
      have h1 := @total_vector_integral_subtract R T Z NZ hNZ nu hnu
        (f (a+hs n)) (f a) (F (a+hs n)) (F a) (hF (hs n) (hhs n).1) hFa.
      have h2 := @total_vector_integral_subtract R T Z NZ hNZ nu hnu
        (fun y => f (a+hs n) y-f a y) (fun y => Df a y (hs n)) _ _ h1 (hL (hs n)).
      exact: (@total_vector_integral_scale R T Z NZ hNZ nu hnu _ _ (c n) h2).
    have hz := dgpr_integral_zero (hL 0).
    have hdom n y : NZ (q n y-0 *: Df a y 0) <= g y + g y.
      rewrite scale0r subr0 /q (real_seminorm_scale hNZ.1) (gtr0_norm (hcpos n)).
      have hrn : NX (hs n) < r := (hhs n).1.
      pose U := [set x | NX (x-a) <= NX (hs n)].
      have hU : is_inner_convex U := @norm_ball_inner_convex R X NX hNX a (NX (hs n)).
      have hdiff x : U x -> exists L0 : Hom X Z,
          has_norm_differential NX NZ A (fun w => f w y) x L0 /\
          forall v, NZ (L0 v) <= g y * NX v.
        move=> hx; have hxr : NX (x-a) < r := le_lt_trans hx hrn.
        have hxa : a+(x-a) = x by rewrite addrC subrK.
        exists (Df x y); split.
        - by have := hD (x-a) y hxr; rewrite hxa.
        - by move=> v; have := hbound (x-a) y v hxr; rewrite hxa.
      have hUa : U a.
        rewrite /U /= subrr hNX0; exact: real_seminorm_nonnegative hNX.1 _.
      have hUx : U (a+hs n) by rewrite /U /= addrAC subrr add0r lexx.
      have hmv := @norm_differential_convex_bound R X Z NX NZ hNX hNZ A U
        (fun w => f w y) (g y) hU (hgpos y (hs n) (hpos n)) hdiff (a+hs n) a hUx hUa.
      rewrite addrAC subrr add0r in hmv.
      have htri : NZ (f (a+hs n) y-f a y-Df a y (hs n)) <=
          NZ (f (a+hs n) y-f a y)+NZ (Df a y (hs n)).
        rewrite -[NZ (Df a y (hs n))](real_seminorm_negate hNZ.1).
        exact: real_seminorm_triangle hNZ.1 _ _.
      have hsum : NZ (f (a+hs n) y-f a y)+NZ (Df a y (hs n)) <=
          (g y+g y)*NX (hs n).
        by rewrite mulrDl; apply: lerD=> //; exact: hba.
      have hfin := le_trans htri hsum.
      rewrite -(ler_pM2l (hcpos n)) hcancel in hfin; exact: hfin.
    have hpoint : measure_almost_everywhere nu [set y | forall eta : R, 0 < eta ->
        exists N : nat, forall m, (N <= m)%N -> NZ (q m y-0 *: Df a y 0) < eta].
      apply: (@measure_almost_everywhere_mono R T nu hnu setT _ _
        (measure_almost_everywhere_true hnu))=> y _ eta heta.
      have heta2 : 0 < eta/2 by rewrite divr_gt0.
      have [d [hd hrem]] := norm_differential_remainder (hDa y) heta2.
      have [N hN] := dgpr_reciprocal_eventually hd.
      exists N=> m hm.
      have hsm : NX (hs m) < d := lt_trans (hhs m).2.1 (hN m hm).
      have hAm : A (a+hs m) := hA (hs m) (hhs m).1.
      have hle := hrem (hs m) hAm hsm.
      rewrite -(ler_pM2l (hcpos m)) hcancel in hle.
      rewrite scale0r subr0 /q (real_seminorm_scale hNZ.1) (gtr0_norm (hcpos m)).
      apply: (le_lt_trans hle); lra.
    have [N hN] := @total_vector_integral_dominated_limit R T Z NZ hNZ nu hnu
      q (fun y => 0 *: Df a y 0) s 0 (fun y => g y + g y) hq hz hgg hdom hpoint e he.
    have hsN := hN N (leqnn N).
    rewrite subr0 /s (real_seminorm_scale hNZ.1) (gtr0_norm (hcpos N)) in hsN.
    have [_ [_ [_ hlt]]] := hhs N.
    rewrite -(ltr_pM2l (hcpos N)) hcancel in hlt.
    by have := lt_trans hlt hsN; rewrite ltxx.
  have [d [hd hgood]] := hc.
  exists d; split=> // h hAh hh.
  rewrite leNgt; apply/negP=> hlt; exact: (hgood h hh (conj hAh hlt)).
Qed.

(** Source for [dgpr_parameter_integral_class_one]: the class 1 assertion
    of differentiation under the integral sign in the blueprint proofs of
    lem:heat_extension(1) and lem:classes(cl:dt). Suppose U is open, every
    map f(.,y) is of class 1 on U with derivative field Df(.,y), the
    differentials are bounded near each point of U by a nu summable function,
    F(x) = int f(x,y) d nu y and DF(x)(v) = int Df(x,y)(v) d nu y for x in U.
    Then F is of class 1 on U with derivative field DF; the continuity of
    DF follows from Lebesgue's bounded convergence theorem, Federer 2.4.9. *)
Theorem dgpr_parameter_integral_class_one (U : set X) (f : X -> T -> Z)
    (Df : X -> T -> Hom X Z) (F : X -> Z) (DF : X -> Hom X Z) :
  (forall x, U x -> norm_domain_interior NX U x) ->
  (forall x, U x -> dgpr_has_integral (f x) (F x)) ->
  (forall x v, U x -> dgpr_has_integral (fun y => Df x y v) (DF x v)) ->
  (forall y, is_norm_class_one_field NX NZ U (fun x => f x y) (fun x => Df x y)) ->
  (forall x, U x -> exists (r : R) (g : T -> R), 0 < r /\ summable_real_functions nu g /\
    forall h y v, NX h < r -> U (x+h) -> NZ (Df (x+h) y v) <= g y * NX v) ->
  is_norm_class_one_field NX NZ U F DF.
Proof.
move=> hU hF hDF hf hloc.
have hNX0 : NX 0 = 0 := real_seminorm_zero hNX.1.
have hlocal a : U a -> exists (rr : R) (g : T -> R), 0 < rr /\
    summable_real_functions nu g /\ (forall h, NX h < rr -> U (a+h)) /\
    forall h y v, NX h < rr -> NZ (Df (a+h) y v) <= g y * NX v.
  move=> ha; have [r0 [hr0 hball]] := hU a ha.
  have [r [g [hr [hg hb]]]] := hloc a ha.
  exists (Num.min r r0), g; split; first by rewrite lt_min hr hr0.
  split=> //; split.
  - by move=> h; rewrite lt_min=> /andP [_ h2]; exact: hball.
  - move=> h y v; rewrite lt_min=> /andP [h1 h2]; exact: (hb h y v h1 (hball h h2)).
have hdiff a : U a -> has_norm_differential NX NZ U F a (DF a).
  move=> ha; have [rr [g [hrr [hg [hball hb]]]]] := hlocal a ha.
  apply: (@dgpr_parameter_integral_differential U f Df g F (DF a) a rr hrr hball).
  - by move=> h hh; exact: hF (hball h hh).
  - by move=> v; exact: hDF.
  - by move=> h y hh; exact: (norm_class_one_differential (hf y) (hball h hh)).
  - exact: hg.
  - exact: hb.
split.
- move=> a ha; split; first exact: hU.
  move=> e he; exact: (norm_differential_continuous_at hNZ (hdiff a ha) he).
- exact: hdiff.
- move=> a ha e he.
  have [rr [g [hrr [[b hgb] [hball hb]]]]] := hlocal a ha.
  have hgg : summable_real_functions nu (fun y => g y + g y).
    by apply: (@summable_real_add R T nu hnu g g); exists b.
  have h0 : NX 0 < rr by rewrite hNX0.
  have hba y v : NZ (Df a y v) <= g y * NX v.
    by have := hb 0 y v h0; rewrite addr0.
  pose B h := exists v, U (a+h) /\ e * NX v < NZ ((DF (a+h)-DF a) v).
  have hc : exists d : R, 0 < d /\ forall h, NX h < d -> ~ B h.
    apply: (dgpr_sequence_contradiction hrr)=> hs hhs.
    have hB n : exists v, U (a+hs n) /\ e * NX v < NZ ((DF (a+hs n)-DF a) v).
      exact: (hhs n).2.2.
    have [vs hvs] := choice hB.
    have hpos n : 0 < NX (vs n).
      rewrite (real_norm_positive hNX.1 hNX.2); apply/negP=> /eqP h0n.
      have [_ hlt] := hvs n; move: hlt.
      rewrite h0n linear0 (real_seminorm_zero hNZ.1) hNX0 mulr0.
      by rewrite ltxx.
    pose c n := (NX (vs n))^-1.
    have hcpos n : 0 < c n by rewrite /c invr_gt0.
    have hcancel n (t : R) : c n * (t * NX (vs n)) = t.
      by rewrite /c mulrCA mulVf ?mulr1 //; exact: lt0r_neq0 (hpos n).
    pose q n y := c n *: (Df (a+hs n) y (vs n)-Df a y (vs n)).
    pose s n := c n *: (DF (a+hs n) (vs n)-DF a (vs n)).
    have hq n : dgpr_has_integral (q n) (s n).
      have h1 := @total_vector_integral_subtract R T Z NZ hNZ nu hnu
        (fun y => Df (a+hs n) y (vs n)) (fun y => Df a y (vs n)) _ _
        (hDF (a+hs n) (vs n) (hvs n).1) (hDF a (vs n) ha).
      exact: (@total_vector_integral_scale R T Z NZ hNZ nu hnu _ _ (c n) h1).
    have hz := dgpr_integral_zero (hDF a 0 ha).
    have hdom n y : NZ (q n y-0 *: Df a y 0) <= g y + g y.
      rewrite scale0r subr0 /q (real_seminorm_scale hNZ.1) (gtr0_norm (hcpos n)).
      have htri : NZ (Df (a+hs n) y (vs n)-Df a y (vs n)) <=
          NZ (Df (a+hs n) y (vs n))+NZ (Df a y (vs n)).
        rewrite -[NZ (Df a y (vs n))](real_seminorm_negate hNZ.1).
        exact: real_seminorm_triangle hNZ.1 _ _.
      have hsum : NZ (Df (a+hs n) y (vs n))+NZ (Df a y (vs n)) <=
          (g y+g y)*NX (vs n).
        rewrite mulrDl; apply: lerD; last exact: hba.
        exact: (hb (hs n) y (vs n) (hhs n).1).
      have hfin := le_trans htri hsum.
      rewrite -(ler_pM2l (hcpos n)) hcancel in hfin; exact: hfin.
    have hpoint : measure_almost_everywhere nu [set y | forall eta : R, 0 < eta ->
        exists N : nat, forall m, (N <= m)%N -> NZ (q m y-0 *: Df a y 0) < eta].
      apply: (@measure_almost_everywhere_mono R T nu hnu setT _ _
        (measure_almost_everywhere_true hnu))=> y _ eta heta.
      have heta2 : 0 < eta/2 by rewrite divr_gt0.
      have [d [hd hcont]] := norm_class_one_continuity (hf y) ha heta2.
      have [N hN] := dgpr_reciprocal_eventually hd.
      exists N=> m hm.
      have hsm : NX (hs m) < d := lt_trans (hhs m).2.1 (hN m hm).
      have hle := hcont (hs m) (hvs m).1 hsm (vs m).
      rewrite -(ler_pM2l (hcpos m)) hcancel in hle.
      rewrite scale0r subr0 /q (real_seminorm_scale hNZ.1) (gtr0_norm (hcpos m)).
      apply: (le_lt_trans hle); lra.
    have [N hN] := @total_vector_integral_dominated_limit R T Z NZ hNZ nu hnu
      q (fun y => 0 *: Df a y 0) s 0 (fun y => g y + g y) hq hz hgg hdom hpoint e he.
    have hsN := hN N (leqnn N).
    rewrite subr0 /s (real_seminorm_scale hNZ.1) (gtr0_norm (hcpos N)) in hsN.
    have [_ hlt] := hvs N.
    rewrite -(ltr_pM2l (hcpos N)) hcancel in hlt.
    by have := lt_trans hlt hsN; rewrite ltxx.
  have [d [hd hgood]] := hc.
  exists d; split=> // h hUh hh v.
  rewrite leNgt; apply/negP=> hlt; apply: (hgood h hh); exists v; split=> //.
Qed.

(** Source for [dgpr_integral_hom_exists]: the derivative int D_x f(x,y) d nu y
    in the blueprint proof of lem:heat_extension(1) is a linear map. If the
    integrals int k(y)(v) d nu y exist for every v, they are the values of
    some L in Hom(X,Z), by the linearity and uniqueness of the integral of
    Federer 2.4.12, p. 87. *)
Lemma dgpr_integral_hom_exists (k : T -> Hom X Z) :
  (forall v, exists z, dgpr_has_integral (fun y => k y v) z) ->
  exists L : Hom X Z, forall v, dgpr_has_integral (fun y => k y v) (L v).
Proof.
move=> hk; have [I hI] := choice hk.
have hlin : linear I.
  move=> c v w.
  have h1 := @total_vector_integral_scale R T Z NZ hNZ nu hnu _ _ c (hI v).
  have h2 := @total_vector_integral_add R T Z NZ hNZ nu hnu _ _ _ _ h1 (hI w).
  have he : (fun y => c *: k y v+k y w) = (fun y => k y (c *: v+w)).
    by apply: funext=> y; rewrite linearP.
  rewrite he in h2.
  exact: (@measure_vector_integral_unique R T Z NZ hNZ nu _ _ _ (hI (c *: v+w)) h2).
exists (@HomMap R X Z I (asboolT hlin))=> v; exact: hI.
Qed.
End ParameterIntegral.
