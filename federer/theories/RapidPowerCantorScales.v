(** Federer (1969), 3.2.40, p. 276: prove local existence
    of sufficiently rapid schedules with the original split
    recurrence. Auxiliary choices stay inside the existence
    proof; no global chosen schedule is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  reals lra.
From Federer Require Import RealPower PowerConcaveIntervalGauge
  CantorSplitRadiusUP CantorSplitRadius RapidPowerCantorScalesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [rapid_power_cantor_split_exists]: supporting one
    sufficiently rapid subdivision step in Federer 3.2.40,
    p. 276. Archimedean integers give the growth bound; the
    earlier opaque split radius gives the actual child width. *)
Lemma rapid_power_cantor_split_exists (R:realType) (c m d:R) j:
  0<c ->0<m ->m<1 ->0<d ->exists (n:nat) (s:R),
    (j.+2<=n)%N /\is_cantor_split_radius (fun t=>c*real_power t m) d n s /\
    j.+1%:R<=n%:R*real_power d (1-2 * m).
Proof.
move=>hc hm hm1 hd.
pose w:=real_power d (1-2 * m).
have hw:0<w:=@real_power_strictly_positive R d (1-2 * m) hd.
have hJ:(0<(j.+1%:R:R)) by rewrite ltr0n.
have hRatio:0<=j.+1%:R/w.
  apply:ltW; by rewrite divr_gt0.
pose N:=Num.bound (j.+1%:R/w).
pose n:=(j.+2+N)%N.
have hn:(j.+2<=n)%N by rewrite /n leq_addr.
have hj2:(2<=j.+2)%N by [].
have hn2:(2<=n)%N:=leq_trans hj2 hn.
have hBound:j.+1%:R/w<N%:R:=archi_boundP hRatio.
have hN:(N%:R:R)<=n%:R by rewrite ler_nat /n leq_addl.
have hGrowth:j.+1%:R<=n%:R*w.
  rewrite -ler_pdivrMr //; exact:ltW (lt_le_trans hBound hN).
pose hg:=power_concave_interval_gauge hc hm hm1.
pose s:=@cantor_split_radius R _ hg d n hd hn2.
exists n,s; split=>//; split; first exact:cantor_split_radius_specification.
exact hGrowth.
Qed.

(** Source for [rapid_power_cantor_scales_exist]: supporting existence
    of the schedule used by Federer 3.2.40, p. 276. The
    independent recurrence and quantitative growth laws precede
    this proof. Recursive states and choices remain local.
    The construction works for every 0<m<1, including the
    subcritical and critical exponents needed by the example. *)
Theorem rapid_power_cantor_scales_exist (R:realType) (c m:R):
  0<c ->0<m ->m<1 ->exists n s,is_rapid_power_cantor_scales c m n s.
Proof.
move=>hc hm hm1.
pose P:={d:R|0<d}.
pose StepLaw (p:nat*P) (q:nat*P):=
  (p.1.+2<=q.1)%N /\
  is_cantor_split_radius (fun t=>c*real_power t m) (sval p.2) q.1 (sval q.2) /\
  p.1.+1%:R<=q.1%:R*real_power (sval p.2) (1-2 * m).
have hExist (p:nat*P):exists q:nat*P,StepLaw p q.
  have [n [s [hn [hs hGrow]]]]:=@rapid_power_cantor_split_exists R c m (sval p.2) p.1
    hc hm hm1 (svalP p.2).
  exists (n,exist (fun d:R=>0<d) s (cantor_split_radius_bounds hs).1).
  by split=>//; split.
have [step hStep]:=choice hExist.
pose d0:P:=exist (fun d:R=>0<d) 1 (@ltr01 R).
pose u:=fix u (j:nat):P:=match j with
  |0%N=>d0
  |j'.+1=>(step (j',u j')).2
  end.
exists (fun j=>(step (j,u j)).1),(fun j=>sval (u j)); constructor.
- reflexivity.
- move=>j; exact:(hStep (j,u j)).1.
- move=>j; exact:(hStep (j,u j)).2.1.
- move=>j; exact:(hStep (j,u j)).2.2.
Qed.
