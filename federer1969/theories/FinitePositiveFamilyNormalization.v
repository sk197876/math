(** Federer (1969), 3.1.13, p. 225:
    normalization of the nonnegative locally finite
    bump sum. These algebraic statements depend
    only on finite-sum laws, not on a
    summation implementation or a series convergence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import FiniteFamilySumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section PositiveSum.
Variable R : realType.
Variable X : Type.
Variable J : choiceType.
Variables (U : X->Prop) (I : J->Prop).
Variables (f : J->X->R) (g : X->R).
Hypothesis hfin : finite_active_family_on U I f.
Hypothesis hsum : is_finite_family_sum_on U I f g.
Hypothesis hnonneg : forall j, I j -> forall x, U x -> 0<=f j x.

(** Source for [finite_nonnegative_family_sum_nonnegative]:
    nonnegativity of the bump sum u,
    supporting Federer 3.1.13, p. 225. *)
Lemma finite_nonnegative_family_sum_nonnegative x : U x -> 0<=g x.
Proof.
move=>hx; have [F [hFI hF]] := hfin hx.
rewrite (hsum hx hFI hF) big_seq_fsetE.
apply: sumr_ge0=>i _; exact: hnonneg (val i) (hFI _ (valP i)) x hx.
Qed.

(** Source for [finite_nonnegative_family_sum_term_bound]:
    each nonnegative bump is at most their
    sum, supporting 0<=v_s<=1 in
    Federer 3.1.13, p. 225. *)
Lemma finite_nonnegative_family_sum_term_bound j x :
  I j -> U x -> f j x<=g x.
Proof.
move=>hj hx; have [F [hFI hF]] := hfin hx.
case hjF:(j \in F).
- rewrite (hsum hx hFI hF) big_seq_fsetE
    (bigD1 ([` hjF]%fset)) //= lerDl.
  apply: sumr_ge0=>i _; exact: hnonneg (val i) (hFI _ (valP i)) x hx.
- have hn : j \notin F by rewrite hjF.
  rewrite (hF j hj hn); exact: (finite_nonnegative_family_sum_nonnegative hx).
Qed.

(** Source for [finite_nonnegative_family_sum_plateau_bound]:
    u(x)>=1 because at least one
    bump equals one at x, Federer
    3.1.13, p. 225. *)
Lemma finite_nonnegative_family_sum_plateau_bound x :
  U x -> (exists j, I j /\ f j x= 1) -> 1<=g x.
Proof.
move=>hx [j [hj he]]; have hb := finite_nonnegative_family_sum_term_bound hj hx.
by rewrite he in hb.
Qed.

Hypothesis hplateau : forall x, U x -> exists j, I j /\ f j x= 1.

(** Source for [finite_normalized_family_range]:
    v_s=u_s/u takes values in
    [0,1], Federer 3.1.13, p. 225. *)
Theorem finite_normalized_family_range j x :
  I j -> U x -> 0<=f j x/g x<=1.
Proof.
move=>hj hx.
have hgl := finite_nonnegative_family_sum_plateau_bound hx (hplateau hx).
have hg : 0<g x := lt_le_trans ltr01 hgl.
apply/andP; split.
- exact: (divr_ge0 (hnonneg hj hx) (ltW hg)).
- rewrite ler_pdivrMr // mul1r; exact: (finite_nonnegative_family_sum_term_bound hj hx).
Qed.

(** Source for [finite_normalized_family_sum_one]:
    the normalized functions sum to one on
    U, Federer 3.1.13, p. 225.
    The result uses the same abstract finite
    evaluation laws as the unnormalized family. *)
Theorem finite_normalized_family_sum_one :
  is_finite_family_sum_on U I (fun j x=>f j x/g x) (fun _=>1).
Proof.
move=>x hx F hFI hF.
have hgl := finite_nonnegative_family_sum_plateau_bound hx (hplateau hx).
have hg : 0<g x := lt_le_trans ltr01 hgl.
have hne : g x!=0 := lt0r_neq0 hg.
have hF' j : I j -> j \notin F -> f j x=0.
  move=>hj hn; have hz := hF j hj hn.
  have hh := congr1 (fun y=>y*g x) hz.
  by rewrite divfK // mul0r in hh.
have he := hsum hx hFI hF'.
rewrite -mulr_suml -he; symmetry; exact: (divff hne).
Qed.
End PositiveSum.
