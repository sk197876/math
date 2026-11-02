(** Federer (1969), 3.1.20, pp. 232–233: local finiteness
    makes the patching sequence eventually stationary near every
    point. Points of B enter the eventual domain permanently. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric LocalRetractionUP RetractionPatchingUP
  StationaryRetractionUP LocallyFiniteFamilyUP BinaryWordEnumerationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section Stabilization.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variables (B U:set X) (P Q W:nat->set X) (f:nat->X->X) (k:nat).
Hypothesis hS:is_retraction_patching_sequence hNX B U P Q W f k.

(** Source for [patching_stabilizes_off_tail]: the domain and
    value equations after all remaining P_i miss a neighbourhood,
    Federer 3.1.20, p. 233. This induction does not assume that
    the domains W_i are monotone away from B. *)
Lemma patching_stabilizes_off_tail (O:set X) d :
  (forall i,(d<=i)%N -> forall x,O x -> ~P i x) ->
  forall i,(d<=i)%N -> forall x,O x ->
    (W i x <-> W d x) /\ (W d x -> f i x=f d x).
Proof.
move=>hoff i hdi.
have [l hi]:exists l,i=(d+l)%N by exists (i-d)%N; rewrite subnKC.
subst i; clear hdi.
elim:l=>[|l ih] x hx.
- rewrite addn0; split; [exact: iff_refl|by move=>hw].
- rewrite addnS.
  have hle:(d<=d+l)%N:=leq_addr l d.
  have hn:=hoff (d+l)%N hle x hx.
  have hs:=@patching_successor R X NX hNX B U P Q W f k hS (d+l)%N.
  have hd:=@retraction_step_domain_off R X NX hNX B U (P (d+l)%N) (Q (d+l)%N)
    (W (d+l)%N) (W (d+l).+1) (f (d+l)%N) (f (d+l).+1) k hs x hn.
  have [hWi hfi]:=ih x hx; split.
  + split=>hw; [exact: hWi.1 (hd.1 hw)|exact: hd.2 (hWi.2 hw)].
  + move=>hw.
    have hf:=@retraction_step_values_off R X NX hNX B U (P (d+l)%N) (Q (d+l)%N)
      (W (d+l)%N) (W (d+l).+1) (f (d+l)%N) (f (d+l).+1) k hs x (hWi.2 hw) hn.
    exact (eq_trans hf (hfi hw)).
Qed.

(** Source for [patching_locally_stationary]: locally finitely
    many P_i affect a neighbourhood, so the domains and maps
    stabilize there, the final argument of Federer 3.1.20,
    p. 233. The previously proved local finiteness of 3.1.13
    supplies the finite set of indices. *)
Lemma patching_locally_stationary :
  @is_locally_finite_family_on [the topologicalType of real_norm_metric_space hNX]
    [the choiceType of (nat:Type)] U setT P ->
  forall x,U x -> exists (O:set X) d,
    @open [the topologicalType of real_norm_metric_space hNX] O /\ O x /\
    forall i,(d<=i)%N -> forall y,O y ->
      (W i y <-> W d y) /\ (W d y -> f i y=f d y).
Proof.
move=>hLF x hx.
have [O [hO [hxO hfin]]]:=hLF x hx.
have [d hd]:=finite_natural_set_upper_bound hfin.
exists O,d; split=>//; split=>//.
apply: patching_stabilizes_off_tail=>i hi y hy hPi.
have hm:(i<d)%N:=hd i (conj I (ex_intro _ y (conj hy hPi))).
have hh:(d<d)%N:=leq_ltn_trans hi hm.
by rewrite ltnn in hh.
Qed.

(** Source for [patching_B_membership_step]: points of B
    already in W_i remain in W_(i+1), the fixed-set equation
    in Federer 3.1.20, p. 232. The whole W_i need not be monotone. *)
Lemma patching_B_membership_step i x : B x -> W i x -> W i.+1 x.
Proof.
move=>hb hw.
have hs:=@patching_successor R X NX hNX B U P Q W f k hS i.
have he:=retraction_step_fixed_set hs.
have hh:(B `&` (W i `|` Q i)) x by split=>//; by left.
rewrite -he in hh; exact hh.2.
Qed.

(** Source for [patching_B_membership_later]: the inclusion of
    B intersect W_j in all subsequent B intersect W_i, supporting
    the eventual-domain inclusion of Federer 3.1.20, p. 232. *)
Lemma patching_B_membership_later j i x : (j<=i)%N -> B x -> W j x -> W i x.
Proof.
move=>hji hb hw.
have [l hi]:exists l,i=(j+l)%N by exists (i-j)%N; rewrite subnKC.
subst i; clear hji; elim:l=>[|l ih]; first by rewrite addn0.
rewrite addnS; exact: patching_B_membership_step hb ih.
Qed.

(** Source for [patching_eventual_domain_contains_B]: the displayed
    containment B subset A in Federer 3.1.20, p. 232: a point
    covered by Q_j is in W_(j+1) and remains in every later domain. *)
Lemma patching_eventual_domain_contains_B :
  (forall b,B b -> exists j,Q j b) -> B `<=` eventual_open_domain W.
Proof.
move=>hcover b hb; have [j hj]:=hcover b hb.
have hs:=@patching_successor R X NX hNX B U P Q W f k hS j.
have hw:=@retraction_step_new_domain R X NX hNX B U (P j) (Q j)
  (W j) (W j.+1) (f j) (f j.+1) k hs b hj.
exists j.+1=>i hi; exact: patching_B_membership_later hi hb hw.
Qed.
End Stabilization.
