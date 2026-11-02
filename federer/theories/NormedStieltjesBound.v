(** Federer (1969), 3.1.11, p. 221:
    the Taylor remainder is bounded using the
    total decrease of its scalar integrator.
    This is the normed-vector version of the
    Stieltjes estimate in 2.5.17, p. 111. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import RealNormUP StieltjesSums StieltjesIntegral NormedStieltjesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_stieltjes_sum_decreasing_bound]:
    the norm of a tagged sum is bounded by
    the integrand bound times the total decrease,
    supporting Federer 3.1.11, p. 221,
    from the sum estimate of 2.5.17, p. 111. *)
Lemma normed_stieltjes_sum_decreasing_bound (R : realType)
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (f : R->Y) (g : R->R) (a b M : R) (w : seq R) :
  is_tagged_partition a b w ->
  (forall t, a<=t<=b -> NY (f t)<=M) ->
  (forall s t, a<=s -> s<=t -> t<=b -> g t<=g s) ->
  NY (normed_stieltjes_sum f g w)<=M*(g a-g b).
Proof.
have [n] := ubnP (size w).
elim: n w a=> // n ih [|t [|u [|t' rest]]] a hsize hw hM hg.
- by case: hw=> [_ [hodd _]].
- have [_ [_ [ht hb]]] := hw; move: ht hb=> /= -> <-.
  by rewrite /= (real_seminorm_zero hNY.1) subrr mulr0.
- by case: hw=> [_ [hodd _]].
- have [t'' [rest' [he [hat [htu [hut' htail]]]]]] := tagged_partition_tail hw.
  case: he=> ht'' hrest'; subst t'' rest'.
  have hs : (size (t'::rest)<n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
  have htt' : t<=t' := le_trans htu hut'.
  have ht'b : t'<=b.
    by have /andP [_ hh] := tagged_partition_points_bounds htail (tagged_partition_a_mem htail).
  have hat' : a<=t' by rewrite hat.
  have hMtail z : t'<=z<=b -> NY (f z)<=M.
    move=>/andP [hz hzb]; apply: hM; rewrite hzb andbT.
    exact: le_trans hat' hz.
  have hgtail s z : t'<=s -> s<=z -> z<=b -> g z<=g s.
    move=> hts hsz hzb; exact: hg s z (le_trans hat' hts) hsz hzb.
  have hrest := ih (t'::rest) t' hs htail hMtail hgtail.
  have hu : a<=u<=b by rewrite hat htu (le_trans hut' ht'b).
  have hdec : g t'<=g t.
    apply: hg=> //; by rewrite hat.
  have hnonneg : 0<=g t-g t' by rewrite subr_ge0.
  have hfirst : NY ((g t'-g t)*:f u)<=M*(g t-g t').
    rewrite (real_seminorm_scale hNY.1) (distrC (g t') (g t))
      (ger0_norm hnonneg).
    have hh := ler_wpM2l hnonneg (hM u hu).
    by rewrite [M*(g t-g t')]mulrC.
  change (NY ((g t'-g t)*:f u+normed_stieltjes_sum f g (t'::rest))<=M*(g a-g b)).
  apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  apply: le_trans (lerD hfirst hrest) _.
  rewrite hat; have heq : M*(g t-g t')+M*(g t'-g b)=M*(g t-g b) by ring.
  by rewrite heq.
Qed.

(** Source for [normed_stieltjes_integral_decreasing_bound]:
    the Taylor integral estimate in Federer
    3.1.11, p. 221, follows by passing
    the finite-sum bound to the actual norm limit.
    Neither completeness nor an extra existence
    hypothesis for other integrals is required. *)
Theorem normed_stieltjes_integral_decreasing_bound (R : realType)
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (f : R->Y) (g : R->R) (a b M : R) (v : Y) :
  has_normed_stieltjes_integral NY f g a b v ->
  (forall t, a<=t<=b -> NY (f t)<=M) ->
  (forall s t, a<=s -> s<=t -> t<=b -> g t<=g s) ->
  NY v<=M*(g a-g b).
Proof.
move=> [hab hi] hM hg; apply/ler_addgt0Pr=>e he.
have [d [hd hb]] := hi e he.
have [n hn] := uniform_mesh_small hab hd.
pose w := uniform_partition a b n.
have hw : is_tagged_partition a b w := uniform_partition_is n hab.
have hm : tagged_mesh_lt d w := uniform_partition_mesh (hn n (leqnn n)).
have hclose := hb w hw hm.
have hbound := normed_stieltjes_sum_decreasing_bound hNY hw hM hg.
have heq : v=(v-normed_stieltjes_sum f g w)+normed_stieltjes_sum f g w.
  by rewrite subrK.
have htri := real_seminorm_triangle hNY.1
  (v-normed_stieltjes_sum f g w) (normed_stieltjes_sum f g w).
rewrite -heq (real_seminorm_subtract hNY.1) in htri.
have hh := le_trans htri (lerD (ltW hclose) hbound).
by rewrite addrC in hh.
Qed.
