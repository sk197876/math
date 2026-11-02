(** Federer (1969), 3.1.15, p. 227:
    the sets of points a of a closed set E where the top
    differential is differentiable with derivative T(a) at the
    uniform rate 1/(j+1) on the punctured ball of radius 1/(q+1).
    They are closed, increase with q, exhaust the points of
    differentiability, and their intersection over j consists of
    points of differentiability; they realise eta_q(a)<=1/(j+1). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RealNormUP ArchimedeanReciprocal NormDifferentialUP NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section UniformSets.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable V : lmodType R.
Variable NV : V->R.
Hypothesis hNV : is_real_norm NV.
Variable B : set X.
Variable phi : X->V.
Hypothesis hphi : norm_class_zero N NV B phi.
Variable E : set X.
Hypothesis hE : closed E.
Hypothesis hEB : E `<=` B.
Variable T : X->Hom X V.
Hypothesis hTb : forall a, E a -> norm_bounded_linear N NV (T a).
Hypothesis hT : forall a, E a -> forall e : R, 0<e -> exists d : R, 0<d /\
  forall b, E b -> N (b-a)<d -> forall h, NV ((T b-T a) h)<=e*N h.

(** Source for [uniform_set]:
    {a in E : eta_q(a)<=1/(j+1)}, where eta_q(a) is the supremum of
    ||D^k f(x)-D^k f(a)-<x-a,D D^k f(a)>||/|x-a| over the punctured
    open ball of radius 1/(q+1) about a within the domain,
    Federer 3.1.15, p. 227. *)
Definition uniform_set (q j : nat) : set X :=
  [set a | E a /\ forall x, B x -> 0<N (x-a) -> N (x-a)<(q.+1%:R)^-1 ->
    NV (phi x-phi a-T a (x-a))<=(j.+1%:R)^-1*N (x-a)].

(** Source for [uniform_set_subset]:
    the sets lie in E, Federer 3.1.15, p. 227. *)
Lemma uniform_set_subset q j : uniform_set q j `<=` E.
Proof. by move=>a [ha _]. Qed.

(** Source for [uniform_set_monotone]:
    eta_q decreases with q, so the sets increase,
    Federer 3.1.15, p. 227. *)
Lemma uniform_set_monotone q q' j : (q<=q')%N -> uniform_set q j `<=` uniform_set q' j.
Proof.
move=>hq a [ha hrate]; split; first exact ha.
move=>x hx hp hd; apply: hrate=>//.
apply: (lt_le_trans hd); rewrite lef_pV2 ?posrE ?ltr0n // ler_nat; exact: hq.
Qed.

(** Source for [uniform_set_closed]:
    each set {a : eta_q(a)<=1/(j+1)} is closed, since the
    remainders depend continuously on a through D^k f and its
    continuous derivative on E, Federer 3.1.15, p. 227 (the
    Borel property of eta_q). *)
Lemma uniform_set_closed q j : closed (uniform_set q j).
Proof.
have homB : forall (F G : Hom X V) h, (F-G) h=F h-G h.
  move=>F G h; rewrite -[-G]scaleN1r hom_addE hom_scaleE; by rewrite scaleN1r.
have tri : forall p u w : X, N (p-u)<=N (p-w)+N (w-u).
  move=>p u w; have -> : p-u=(p-w)+(w-u) by rewrite addrA subrK.
  exact: (real_seminorm_triangle hN.1).
have h4 : (0:R)<4 by rewrite ltr0n.
have ho : open (~` uniform_set q j).
  rewrite openE=>a ha.
  case: (pselect (E a))=>[haE|haE]; last first.
  - have hoE : open (~` E) := closed_openC hE.
    rewrite openE in hoE.
    exact: (filterS (fun b (hb : ~ E b) (hG : uniform_set q j b)=>hb (uniform_set_subset hG))
      (hoE a haE)).
  have [x [hxB [hpos [hsmall hviol]]]] : exists x, B x /\ 0<N (x-a) /\ N (x-a)<(q.+1%:R)^-1 /\
      (j.+1%:R)^-1*N (x-a)<NV (phi x-phi a-T a (x-a)).
    apply: contrapT=>hnot; apply: ha; split; first exact haE.
    move=>x hx hp hd; rewrite leNgt; apply/negP=>hlt; apply: hnot.
    by exists x.
  set inv : R := (q.+1%:R)^-1 in hsmall *.
  set c : R := (j.+1%:R)^-1.
  set ra := phi x-phi a-T a (x-a).
  set s := NV ra-c*N (x-a).
  have hs : 0<s by rewrite /s subr_gt0.
  have hs4 : 0<s/4 by exact: divr_gt0.
  have hc0 : 0<=c by rewrite /c invr_ge0 ler0n.
  have [[rB [hrB hball]] hcont] := hphi (hEB haE).
  have [d1 [hd1 hphi1]] := hcont (s/4) hs4.
  have [Ca [hCa hTa]] := hTb haE.
  set d2 := s/(4*(Ca+1)).
  have hd2 : 0<d2 by apply: divr_gt0=>//; apply: mulr_gt0=>//; lra.
  have hxa1 : 0<N (x-a)+1 by lra.
  set e3 := s/(4*(N (x-a)+1)).
  have he3 : 0<e3 by apply: divr_gt0=>//; apply: mulr_gt0=>//.
  have [d3 [hd3 hT3]] := hT haE he3.
  set d5 := inv-N (x-a).
  have hd5 : 0<d5 by rewrite /d5 subr_gt0.
  set d6 := s/(4*(c+1)).
  have hd6 : 0<d6 by apply: divr_gt0=>//; apply: mulr_gt0=>//; lra.
  set d := Num.min d1 (Num.min rB (Num.min d2 (Num.min d3 (Num.min (N (x-a))
    (Num.min d5 (Num.min d6 1)))))).
  have hd : 0<d by rewrite /d !lt_min hd1 hrB hd2 hd3 hpos hd5 hd6 ltr01.
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP a _)).
  exists d; first exact hd.
  move=>b hb0 hG.
  have hb : N (a-b)<d by rewrite -inner_metric_distanceE; exact: hb0.
  have hbd := hb; rewrite /d !lt_min in hbd.
  case/andP: hbd=>hb1 /andP [hb2 /andP [hb3 /andP [hb4 /andP [hb5 /andP [hb6 /andP [hb7 hb8]]]]]].
  have hb1' : N (a-b)<d1 := hb1.
  have hb3' : N (a-b)<d2 := hb3.
  have hb4' : N (a-b)<d3 := hb4.
  have hb5' : N (a-b)<N (x-a) := hb5.
  have hb6' : N (a-b)<d5 := hb6.
  have hb7' : N (a-b)<d6 := hb7.
  have hb8' : N (a-b)<1 := hb8.
  clear hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8.
  have [hbE hrate] := hG.
  have hsub : forall p u : X, N (p-u)=N (u-p) by move=>p u; exact: (real_seminorm_subtract hN.1 p u).
  have hba := hsub b a.
  have hxb1 := tri x a b.
  have hxb2 := tri x b a.
  have hposb : 0<N (x-b) by lra.
  have hsmallb : N (x-b)<inv.
    have h6 : N (a-b)<inv-N (x-a) := hb6'.
    move: hxb2 h6; lra.
  have hrb : NV (phi x-phi b-T b (x-b))<=c*N (x-b) := hrate x hxB hposb hsmallb.
  have hab : a+(b-a)=b by rewrite addrCA subrr addr0.
  have h2 : NV (phi b-phi a)<s/4.
    have hbB : B (a+(b-a)) by rewrite hab; exact: (hEB hbE).
    have hbd1 : N (b-a)<d1 by rewrite hba; exact: hb1'.
    have hh := hphi1 (b-a) hbB hbd1; by rewrite hab in hh.
  have hb4'' : N (b-a)<d3 by rewrite hba.
  have h3 : NV ((T b-T a) (x-b))<=e3*N (x-b) := hT3 b hbE hb4'' (x-b).
  have h4' : NV (T a (a-b))<=Ca*N (a-b) := hTa (a-b).
  have hv : (x-b)-(x-a)=a-b by rewrite opprB addrCA [x-b-x]addrAC subrr add0r.
  have b4 : NV (T a (x-b)-T a (x-a))<=Ca*N (a-b) by rewrite -raddfB hv; exact: hTa.
  rewrite homB in h3.
  have hdecomp : ra=(phi x-phi b-T b (x-b))+(phi b-phi a)+(T b (x-b)-T a (x-b))+
      (T a (x-b)-T a (x-a)).
    rewrite /ra; apply/esym.
    by rewrite -addrA subrKA [phi x-phi b-T b (x-b)]addrAC subrKA [phi x-T b (x-b)-phi a]addrAC subrKA.
  have htri4 : NV ra<=NV (phi x-phi b-T b (x-b))+NV (phi b-phi a)+NV (T b (x-b)-T a (x-b))+
      NV (T a (x-b)-T a (x-a)).
    rewrite hdecomp.
    apply: (le_trans (real_seminorm_triangle hNV.1 _ _)); apply: (lerD _ (lexx _)).
    apply: (le_trans (real_seminorm_triangle hNV.1 _ _)); apply: (lerD _ (lexx _)).
    exact: (real_seminorm_triangle hNV.1 _ _).
  have hab0 : 0<=N (a-b) := real_seminorm_nonnegative hN.1 (a-b).
  have hcb : c*N (x-b)<=c*N (x-a)+c*N (a-b) by rewrite -mulrDr; exact: (ler_wpM2l hc0 hxb2).
  have hc1 : 0<c+1 by lra.
  have hc1n : c+1 != 0 := lt0r_neq0 hc1.
  have hd6e : (c+1)*d6=s/4.
    by rewrite /d6 mulrA [(c+1)*s]mulrC -mulrA invfM [(c+1)*(_*_)]mulrCA mulfV // mulr1.
  have hcle : c<=c+1 by rewrite lerDl ler01.
  have hc6 : c*N (a-b)<s/4.
    rewrite -hd6e; apply: (le_lt_trans (ler_wpM2r hab0 hcle)).
    by rewrite (ltr_pM2l hc1).
  have hCa1 : 0<Ca+1 by lra.
  have hCa1n : Ca+1 != 0 := lt0r_neq0 hCa1.
  have hd2e : (Ca+1)*d2=s/4.
    by rewrite /d2 mulrA [(Ca+1)*s]mulrC -mulrA invfM [(Ca+1)*(_*_)]mulrCA mulfV // mulr1.
  have hCale : Ca<=Ca+1 by rewrite lerDl ler01.
  have h4b : Ca*N (a-b)<s/4.
    rewrite -hd2e; apply: (le_lt_trans (ler_wpM2r hab0 hCale)).
    by rewrite (ltr_pM2l hCa1).
  have hxa1n : N (x-a)+1 != 0 := lt0r_neq0 hxa1.
  have he3e : e3*(N (x-a)+1)=s/4.
    by rewrite /e3 -mulrA invfM -mulrA mulVf // mulr1.
  have h3b : e3*N (x-b)<s/4.
    rewrite -he3e (ltr_pM2l he3); lra.
  have hsE : s=NV ra-c*N (x-a) by [].
  have hlt : NV ra<NV ra by lra.
  by rewrite ltxx in hlt.
have hc := open_closedC ho; by rewrite setCK in hc.
Qed.

(** Source for [uniform_set_from_differential]:
    at a point of differentiability of the top differential
    with derivative T(a), eta_q(a)<=1/(j+1) for large q,
    Federer 3.1.15, p. 227 ("lim eta_q(a)=0"). *)
Lemma uniform_set_from_differential (j : nat) (a : X) : E a ->
  has_norm_differential N NV B phi a (T a) -> exists q, uniform_set q j a.
Proof.
move=>ha hd.
have hj : (0:R)<(j.+1%:R)^-1 by rewrite invr_gt0 ltr0n.
have [d [hd0 hrem]] := norm_differential_remainder hd hj.
have [q hq] := real_reciprocal_below hd0.
exists q; split; first exact ha.
move=>x hx hp hsmall.
have hax : a+(x-a)=x by rewrite addrCA subrr addr0.
have hxB : B (a+(x-a)) by rewrite hax.
have hh := hrem (x-a) hxB (lt_trans hsmall hq).
by rewrite hax in hh.
Qed.

(** Source for [uniform_set_to_differential]:
    a point lying in {eta_{q_j}<=1/(j+1)} for every j is a point
    of differentiability with derivative T(a), Federer 3.1.15,
    p. 227. *)
Lemma uniform_set_to_differential (Q : nat->nat) (a : X) :
  (forall j, uniform_set (Q j) j a) -> has_norm_differential N NV B phi a (T a).
Proof.
move=>hQ.
have ha : E a := (hQ 0%N).1.
split.
- exact: (hphi (hEB ha)).1.
- exact: (hTb ha).
- move=>e he.
  have [j hj] := real_reciprocal_below he.
  exists ((Q j).+1%:R)^-1; split; first by rewrite invr_gt0 ltr0n.
  move=>h hB hsmall.
  have hN0 := real_seminorm_nonnegative hN.1 h.
  rewrite le_eqVlt in hN0; case/orP: hN0=>[/eqP h0|hpos].
  + have hz : h=0 by apply: hN.2; rewrite -h0.
    rewrite hz addr0 subrr raddf0 subr0 (real_seminorm_zero hNV.1) (real_seminorm_zero hN.1) mulr0.
    exact: lexx.
  + have hrate := (hQ j).2 (a+h) hB.
    rewrite [a+h-a]addrAC subrr add0r in hrate.
    apply: (le_trans (hrate hpos hsmall)).
    exact: (ler_wpM2r (ltW hpos) (ltW hj)).
Qed.
End UniformSets.
