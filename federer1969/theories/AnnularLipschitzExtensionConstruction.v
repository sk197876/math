(** Private existence proof for Federer's successive Lipschitz extensions,
    3.1.16, p. 228. Downstream proofs use the sealed ball and agreement laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric
  LipschitzUP LipschitzBasic MetricClosedBalls EuclideanClosedBallCompact
  OpenAnnuliClosedUnion CompactDisjointLipschitzUnion KirszbraunTheorem
  AnnularLipschitzExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Construction.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Variables (C : nat->set X) (f : X->Y).
Hypothesis hC : forall i, compact (C i).
Hypothesis hCU : forall i, C i `<=` open_annulus (0:X) i.
Hypothesis hCf : forall i, is_metric_lipschitz (C i) f.

(** Source for [annular_lipschitz_extension_step]: the repeated use of
    2.10.43 in Federer 3.1.16, p. 228. Extend the previous global map
    on the closed ball of radius i together with f on C_i, which is
    disjoint from that ball. Compact separation supplies a finite bound. *)
Lemma annular_lipschitz_extension_step (i : nat) (g : X->Y) :
  is_metric_lipschitz setT g -> exists G : X->Y,
    is_metric_lipschitz setT G /\
    (forall x : X, mdist (0:X) x<=i%:R -> G x=g x) /\
    (forall x, C i x -> G x=f x).
Proof.
move=>hg.
pose B := metric_closed_ball (0:X) (i%:R : R).
pose p x := if pselect (B x) then g x else f x.
have hpg x : B x -> p x=g x by rewrite /p; case: pselect=>// h; contradiction.
have hdis x : B x -> C i x -> False.
  move=>hx hc; have /andP [hi _] := @hCU i x hc.
  change (is_true (mdist (0:X) x<=i%:R)) in hx.
  by have := lt_le_trans hi hx; rewrite ltxx.
have hpf x : C i x -> p x=f x.
  move=>hx; rewrite /p; case: pselect=>// hb; exfalso; exact (hdis x hb hx).
have hBL : is_metric_lipschitz B p.
  have [L [hL [hL0 hb]]] := hg.
  exists L; split=>//; split=>// x y hx hy.
  rewrite (hpg x hx) (hpg y hy); exact (hb x y I I).
have hCL : is_metric_lipschitz (C i) p.
  have [L [hL [hL0 hb]]] := @hCf i.
  exists L; split=>//; split=>// x y hx hy.
  rewrite (hpf x hx) (hpf y hy); exact (hb x y hx hy).
have hp := compact_disjoint_lipschitz_union
  (@euclidean_closed_metric_ball_compact R m 0 i%:R) (@hC i) hdis hBL hCL.
have [G [hG [hagree _]]] := federer_2_10_43 hp.
exists G; split=>//; split.
- move=>x hx; rewrite (hagree x (or_introl hx)); exact: hpg.
- move=>x hx; rewrite (hagree x (or_intror hx)); exact: hpf.
Qed.

(** Source for [annular_lipschitz_extension_exists]: the map h of
    Federer 3.1.16, p. 228, obtained by successive agreeing extensions.
    Their values stabilize on each closed ball. Recursion and choice
    serve only to prove existence of the abstract extension laws. *)
Theorem annular_lipschitz_extension_exists : exists h,
  is_annular_lipschitz_extension C f h.
Proof.
pose State := {g : X->Y | is_metric_lipschitz setT g}.
have hzero : is_metric_lipschitz setT (fun _ : X=>(0:Y)).
  exists 1; split; first exact: ltr01.
  split; first exact: ler01.
  by move=>x y _ _; rewrite mdistxx mul1r mdist_ge0.
pose step (i : nat) (s : State) : State :=
  let q := cid (annular_lipschitz_extension_step i (proj2_sig s)) in
  exist _ (projT1 q) (projT2 q).1.
pose states := fix states (i : nat) : State :=
  match i with 0%N=>exist _ (fun _ : X=>(0:Y)) hzero | j.+1=>step j (states j) end.
pose G i := proj1_sig (states i).
have hG i : is_metric_lipschitz setT (G i) := proj2_sig (states i).
have hstep i : (forall x : X, mdist (0:X) x<=i%:R -> G i.+1 x=G i x) /\
    (forall x, C i x -> G i.+1 x=f x).
  exact (projT2 (cid (annular_lipschitz_extension_step i (proj2_sig (states i))))).2.
have hstable p q : (p<=q)%N -> forall x : X, mdist (0:X) x<=p%:R -> G p x=G q x.
  elim: q=>[|q ih] hpq x hx.
  - have -> : p=0%N by apply/eqP; rewrite eqn0Ngt -leqNgt.
    by [].
  - case: (eqVneq p q.+1)=>[->|hne]; first by [].
    have hpq' : (p<=q)%N by move: hpq; rewrite leq_eqVlt (negPf hne) /= ltnS.
    have hpqR : (p%:R : R)<=q%:R by rewrite ler_nat.
    rewrite (hstep q).1; first exact (ih hpq' x hx).
    exact (le_trans hx hpqR).
have hstable' p q x : mdist (0:X) x<=p%:R -> mdist (0:X) x<=q%:R -> G p x=G q x.
  move=>hp hq; case: (leqP p q)=>hpq.
  - exact (hstable p q hpq x hp).
  - exact (esym (hstable q p (ltnW hpq) x hq)).
have hex x : exists y : Y, forall i : nat, mdist (0:X) x<=i%:R -> y=G i.+1 x.
  have /andP [_ ht] := truncn_itv (mdist_ge0 (0:X) x).
  exists (G (Num.truncn (mdist (0:X) x)).+1 x)=>i hi.
  have hiR : (i%:R : R)<=i.+1%:R by rewrite ler_nat.
  exact (hstable' _ _ x (ltW ht) (le_trans hi hiR)).
have [h hh] := choice hex.
exists h; constructor.
- move=>i x hx.
  have /andP [_ hi] := @hCU i x hx.
  rewrite (hh x i.+1 (ltW hi)).
  rewrite (hstep i.+1).1; first exact ((hstep i).2 x hx).
  exact: ltW hi.
- move=>i.
  have [L [hL [hL0 hb]]] := hG i.+1.
  exists L; split=>//; split=>// x y hx hy.
  rewrite (hh x i hx) (hh y i hy); exact (hb x y I I).
Qed.
End Construction.
