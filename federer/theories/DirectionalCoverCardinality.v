(** Federer (1969), 2.8.11, pp. 147–148: a controlled family meeting a
    distinguished ball, with the displayed radius and neighborhood
    restrictions, has at most 2 zeta+1 members. We follow the two printed
    distance classes with k=(2-eta)/tau. its relaxed inequalities and
    directional definition are not substituted here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology lra.
From Federer Require Import DirectionalLimitationUP ControlledBallParameters
  DirectionalCoverEstimates DirectionalParameterCardinality TwoPartCardinalBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [has_directional_cover_factor]: the two
    strict parameter inequalities in Federer 2.8.11, p. 147:
    1<tau<2-eta and eta+tau/(2-eta)+tau(tau-1)<1.
    Eta's separate bounds are part of directional limitation. *)
Definition has_directional_cover_factor (R : realType) (eta tau : R) :=
  1 < tau /\ tau < 2-eta /\ eta+tau/(2-eta)+tau*(tau-1) < 1.

(** Source for [directional_cover_factor_uniform]: explicit
    witness for the admissible tau in Federer 2.8.11, p. 147.
    The value 33/32 works for every 0<eta<=1/3, spelling out
    "slightly larger than 1". The rational comparisons use
    kernel-checked computation. *)
Lemma directional_cover_factor_uniform (R : realType) (eta : R) :
  0 < eta <= 1/3 -> has_directional_cover_factor eta (ratr (33/32 : rat)).
Proof.
move=> /andP [he he3].
pose t : R := ratr (33/32 : rat).
have h1 : (ratr (1 : rat) : R) = 1 by rewrite rmorph1.
have h0 : (ratr (0 : rat) : R) = 0 by rewrite rmorph0.
have htwo : (ratr (2 : rat) : R) = 2 by rewrite rmorph_nat.
have ht : 1 < t.
  rewrite /t -h1 ltr_rat; by vm_compute.
have hthirdE : (ratr (1/3 : rat) : R) = 1/3.
  by rewrite rmorphM fmorphV rmorph1 rmorph_nat.
have hthird : (1/3 : R) < 1.
  rewrite -hthirdE -h1 ltr_rat; by vm_compute.
have hden : (ratr (5/3 : rat) : R) <= 2-eta.
  have hf : (ratr (5/3 : rat) : R) = 2-1/3.
    rewrite -hthirdE -htwo -rmorphB; congr (ratr _); by vm_compute.
  by rewrite hf lerD2l lerN2.
have hden0 : 0 < (ratr (5/3 : rat) : R).
  rewrite -h0 ltr_rat; by vm_compute.
have hdenpos : 0 < 2-eta := lt_le_trans hden0 hden.
have hupper : t < (ratr (5/3 : rat) : R).
  rewrite /t ltr_rat; by vm_compute.
have hratio : t/(2-eta) <= (ratr ((33/32)/(5/3) : rat) : R).
  rewrite rmorphM fmorphV -/t (ler_pM2l (lt_trans ltr01 ht)).
  by rewrite (@lef_pV2 R _ _ hdenpos hden0).
split=> //; split; first exact: lt_le_trans hupper hden.
have hsum : eta+t/(2-eta)+t*(t-1) <=
    (ratr (1/3+(33/32)/(5/3)+(33/32)*(33/32-1) : rat) : R).
  rewrite rmorphD rmorphD.
  have hterm : (ratr ((33/32)*(33/32-1) : rat) : R) = t*(t-1).
    by rewrite rmorphM rmorphB rmorph1.
  change (eta+t/(2-eta)+t*(t-1) <=
    (ratr (1/3 : rat) : R)+ratr ((33/32)/(5/3) : rat)+ratr ((33/32)*(33/32-1) : rat)).
  rewrite hterm hthirdE.
  exact: lerD (lerD he3 hratio) (lexx _).
apply: le_lt_trans hsum _.
rewrite -h1 ltr_rat; by vm_compute.
Qed.


(** Source for [directional_cover_factor_exists]: the existence
    assertion in Federer 2.8.11, p. 147. It follows from
    the uniform witness above, including eta=1/3. *)
Lemma directional_cover_factor_exists (R : realType) (eta : R) :
  0 < eta <= 1/3 -> exists tau : R, has_directional_cover_factor eta tau.
Proof.
move=> he; exists (ratr (33/32 : rat)); exact: directional_cover_factor_uniform he.
Qed.

(** Source for [directional_near_parameters]: P_1 in the
    proof of Federer 2.8.11, p. 148: 0<rho(a,b)<=kr,
    with k=(2-eta)/tau. The distinguished pair is retained
    as a parameter, so no choice of center or radius is involved. *)
Definition directional_near_parameters (R : realType) (X : metricType R)
    (P : set (X*R)) (p : X*R) (eta tau : R) :=
  [set q | P q /\ 0 < mdist p.1 q.1 <= ((2-eta)/tau)* p.2].

(** Source for [directional_far_parameters]: P_2 in the
    proof of Federer 2.8.11, p. 148: rho(a,b)>kr. *)
Definition directional_far_parameters (R : realType) (X : metricType R)
    (P : set (X*R)) (p : X*R) (eta tau : R) :=
  [set q | P q /\ ((2-eta)/tau)* p.2 < mdist p.1 q.1].

Section Cardinality.
Variable R : realType.
Variable X : metricType R.
Variable A : set X.
Variable xi : \bar R.
Variables eta tau : R.
Variable zeta : nat.
Variable P : set (X*R).
Variable p : X*R.
Hypothesis hlim : is_directionally_limited_at A xi eta zeta.
Hypothesis hfactor : has_directional_cover_factor eta tau.
Hypothesis hP : is_controlled_ball_family tau P.
Hypothesis hp : P p.
Hypothesis hA : forall q, P q -> A q.1.
Hypothesis hlocal : forall q, P q ->
  ((mdist p.1 q.1)%:E < xi)%E /\ mdist p.1 q.1 <= p.2+q.2 /\ p.2/tau < q.2.
Local Notation Near := (directional_near_parameters P p eta tau).
Local Notation Far := (directional_far_parameters P p eta tau).

(** Source for [directional_split_scale_positive]: positivity
    of k r, the threshold in Federer 2.8.11, p. 148.
    Supporting consequence of positive radii and 1<tau<2-eta. *)
Lemma directional_split_scale_positive : 0 < ((2-eta)/tau)* p.2.
Proof.
have [ht [ht2 _]] := hfactor.
have ht0 := lt_trans ltr01 ht.
have h2 := lt_trans ht0 ht2.
by rewrite mulr_gt0 ?divr_gt0 //; exact (@controlled_positive_radii R X tau P hP p hp).
Qed.

(** Source for [directional_near_radial_separation]: the
    j=1 case of Federer 2.8.11, p. 148, ending with
    rho(x,c)>eta rho(a,c). We retain the strict estimate
    before division, then obtain Federer's required weak bound. *)
Lemma directional_near_radial_separation q t : Near q -> Near t -> q <> t ->
  forall x, is_radial_projection_configuration p.1 q.1 t.1 x ->
    eta <= mdist x t.1 / mdist p.1 t.1.
Proof.
move=> [hq /andP [hD0 hD]] [ht /andP [hC0 hC]] hqt x hx.
have [htau [htau2 _]] := hfactor.
have htau0 := lt_trans ltr01 htau.
have hthird : (1/3 : R) < 1 by rewrite ltr_pdivrMr ?ltr0n // mul1r ltr1n.
have heta : eta < 1 := le_lt_trans (andP (directional_separation_range hlim)).2 hthird.
have hpt : p <> t.
  by move=> he; move: hC0; rewrite -he mdistxx ltxx.
have hpR := (@hlocal p hp).2.2.
have hqR := (@hlocal q hq).2.2.
have htR := (@hlocal t ht).2.2.
have hCbig := @controlled_distance_above_lower_bound R X P tau (p.2/tau)
  hP p t hp ht hpt hpR htR.
have hHbig := @controlled_distance_above_lower_bound R X P tau (p.2/tau)
  hP q t hq ht hqt hqR htR.
have hD' : mdist p.1 q.1 <= (2-eta)*(p.2/tau).
  have heq : ((2-eta)/tau)* p.2 = (2-eta)*(p.2/tau).
    by rewrite mulrAC mulrA.
  by rewrite -heq.
have hX := radial_projection_triangle_lower hx.
have hs := @directional_near_scalar_estimate R eta (mdist p.1 t.1)
  (mdist q.1 t.1) (mdist p.1 q.1) (p.2/tau) (mdist x t.1)
  heta hCbig hHbig hD' hX.
rewrite ler_pdivlMr //; exact: ltW hs.
Qed.

(** Source for [directional_far_radial_separation]: the j=2
    case of Federer 2.8.11, p. 148. The inequalities
    r<rho(a,c)/k, t<tau rho(a,c), and
    rho(b,c)-s>t-tau t yield the strict separation. *)
Lemma directional_far_radial_separation q t : Far q -> Far t -> q <> t ->
  forall x, is_radial_projection_configuration p.1 q.1 t.1 x ->
    eta <= mdist x t.1 / mdist p.1 t.1.
Proof.
move=> [hq hD] [ht hC] hqt x hx.
have [htau [htau2 hparam]] := hfactor.
have htau0 := lt_trans ltr01 htau.
have h2 : 0 < 2-eta := lt_trans htau0 htau2.
have hC0 := lt_trans directional_split_scale_positive hC.
have hpt : p <> t.
  by move=> he; move: hC0; rewrite -he mdistxx ltxx.
have hr : p.2 < (tau/(2-eta))* mdist p.1 t.1.
  have hmul : (2-eta)* p.2 < mdist p.1 t.1*tau.
    by move: hC; rewrite mulrAC ltr_pdivrMr.
  by rewrite mulrAC ltr_pdivlMr // mulrC [tau * _]mulrC.
have hrad : t.2 < tau* mdist p.1 t.1.
  have hh := @controlled_distance_above_radius_ratio R X P tau hP p t hp ht hpt.
  by move: hh; rewrite ltr_pdivrMr // mulrC.
have hdiff := @controlled_pair_far_difference R X P tau hP q t hq ht hqt.
have hD' := (@hlocal q hq).2.1.
have hX := radial_projection_triangle_lower hx.
have hs := @directional_far_scalar_estimate R eta (tau/(2-eta)) tau
  (mdist p.1 t.1) (mdist q.1 t.1) (mdist p.1 q.1) p.2 q.2 t.2 (mdist x t.1)
  hC0 htau hparam hr hrad hdiff hD' hX.
rewrite ler_pdivlMr //; exact: ltW hs.
Qed.

(** Source for [federer_2_8_11]: the theorem of Federer
    2.8.11, pp. 147–148, card P<=2 zeta+1. The
    two printed distance classes inherit directional separation;
    controlledness makes projection to centers injective. The
    distinguished pair supplies the remaining one member. *)
Theorem federer_2_8_11 : P #<= [set: 'I_(2*zeta+1)].
Proof.
have hnear : Near #<= [set: 'I_zeta].
  apply: (@directional_parameter_cardinal_bound R X A xi eta tau zeta P Near p.1
    hlim hP (@hA p hp)).
  - by move=> q [hq _].
  - move=> q [hq /andP [hpos _]]; split; first by split; [exact (@hA q hq)|exact: (@hlocal q hq).1].
    by move=> he; move: hpos; rewrite he mdistxx ltxx.
  - exact: directional_near_radial_separation.
have hfar : Far #<= [set: 'I_zeta].
  apply: (@directional_parameter_cardinal_bound R X A xi eta tau zeta P Far p.1
    hlim hP (@hA p hp)).
  - by move=> q [hq _].
  - move=> q [hq hqfar]; split; first by split; [exact (@hA q hq)|exact: (@hlocal q hq).1].
    have hpos := lt_trans directional_split_scale_positive hqfar.
    by move=> he; move: hpos; rewrite he mdistxx ltxx.
  - exact: directional_far_radial_separation.
apply: (@two_part_cardinal_bound [the choiceType of (X*R)%type] P Near Far p zeta _ hnear hfar).
move=> q hq; case: (pselect (q=p))=> [->|hne]; first by left.
right; case: (leP (mdist p.1 q.1) (((2-eta)/tau)* p.2))=> [hsmall|hlarge].
- left; split=> //; apply/andP; split=> //.
  have hcent : q.1 <> p.1.
    move=> he; apply: hne; exact (@controlled_centers_injective R X tau P hP q p hq hp he).
  rewrite mdist_gt0; apply/eqP=> he; apply: hcent; exact: esym he.
- right; by split.
Qed.
End Cardinality.
