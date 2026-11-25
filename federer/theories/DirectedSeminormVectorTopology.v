(** Federer (1969), 4.1.1, p. 344: the seminorm topology is
    locally convex and compatible with the vector operations.
    These supporting proofs apply to any directed family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import RealNormUP OpenFamilyTopologyUP OpenVectorTopologyUP
  DirectedSeminormFamilyUP DirectedSeminormTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SeminormVectorTopology.
Variable R:realType.
Variable E:lmodType R.
Variable I:Type.
Variable p:I->E->R.
Variable O:set (set E).
Hypothesis hp:is_directed_seminorm_family p.
Hypothesis hO:is_seminorm_family_topology p O.

(** Source for [seminorm_family_addition_continuous]: joint
    continuity of addition in E(U,Y), supporting Federer 4.1.1,
    p. 344. The triangle inequality halves a basic radius. *)
Theorem seminorm_family_addition_continuous :
  open_family_jointly_continuous O O O (fun x y=>x+y).
Proof.
move=>x y A hA hxy.
have [i [r [hr hb]]]:=(hO.2 A).1 hA (x+y) hxy.
exists [set u|p i (u-x)<r/2],[set v|p i (v-y)<r/2].
split; first exact:(@seminorm_family_ball_open R E I p O hp hO i x (r/2)).
split; first exact:(@seminorm_family_ball_open R E I p O hp hO i y (r/2)).
have hh:0<r/2 by rewrite divr_gt0 // ltr0n.
split; first by rewrite /= subrr (real_seminorm_zero (directed_seminorm_laws hp i)).
split; first by rewrite /= subrr (real_seminorm_zero (directed_seminorm_laws hp i)).
move=>u v hu hv; apply:hb.
change (is_true (p i (u-x)<r/2)) in hu.
change (is_true (p i (v-y)<r/2)) in hv.
have he:u+v-(x+y)=(u-x)+(v-y) by rewrite opprD addrACA.
rewrite he.
have ht:=real_seminorm_triangle (directed_seminorm_laws hp i) (u-x) (v-y).
have hSum:=ltrD hu hv.
rewrite -splitr in hSum.
exact:le_lt_trans ht hSum.
Qed.

(** Source for [seminorm_family_scaling_continuous]: joint
    continuity of scalar multiplication in the seminorm topology,
    supporting Federer 4.1.1, p. 344. Neither nonzero vectors nor
    nonzero scalars are required. *)
Theorem seminorm_family_scaling_continuous c x A :
  O A -> A (c*:x) -> exists d B,0<d /\ O B /\ B x /\
    forall s y,`|s-c|<d -> B y -> A (s*:y).
Proof.
move=>hA hx.
have [i [r [hr hb]]]:=(hO.2 A).1 hA (c*:x) hx.
have hn:=real_seminorm_nonnegative (directed_seminorm_laws hp i) x.
have hpx:0<p i x+1 by lra.
have hcx:0<`|c|+1 by have:=normr_ge0 c; lra.
pose d:=Num.min 1 (r/(2*(p i x+1))).
pose e:=r/(2*(`|c|+1)).
have hd:0<d by rewrite /d lt_min ltr01 divr_gt0 // mulr_gt0 // ltr0n.
have he:0<e by rewrite /e divr_gt0 // mulr_gt0 // ltr0n.
exists d,[set y|p i (y-x)<e]; split=>//.
split; first exact:(@seminorm_family_ball_open R E I p O hp hO i x e).
split; first by rewrite /= subrr (real_seminorm_zero (directed_seminorm_laws hp i)).
move=>s y hs hy; apply:hb.
change (is_true (p i (y-x)<e)) in hy.
have /andP [hs1 hs2]: (`|s-c|<1) && (`|s-c|<r/(2*(p i x+1))).
  by rewrite -lt_min; exact:hs.
have hsBound:`|s|<`|c|+1.
  have h:=ler_normD (s-c) c.
  rewrite subrK in h; lra.
have hHalf:r/2+r/2=r by rewrite -splitr.
have hxBound:`|s-c|*(p i x+1)<r/2.
  have hTmp:`|s-c|*(2*(p i x+1))<r.
    by move:hs2; rewrite ltr_pdivlMr ?mulr_gt0 // ?ltr0n.
  nra.
have hyBound:(`|c|+1)* p i (y-x)<r/2.
  have hTmp:p i (y-x)*(2*(`|c|+1))<r.
    by move:hy; rewrite /e ltr_pdivlMr ?mulr_gt0 // ?ltr0n.
  nra.
have hEq:s*:y-c*:x=s*:(y-x)+(s-c)*:x.
  by rewrite scalerBr scalerBl addrA subrK.
rewrite hEq.
have hT:=real_seminorm_triangle (directed_seminorm_laws hp i) (s*:(y-x)) ((s-c)*:x).
rewrite !(real_seminorm_scale (directed_seminorm_laws hp i)) in hT.
have hny:=real_seminorm_nonnegative (directed_seminorm_laws hp i) (y-x).
have hs0:=normr_ge0 (s-c).
have hUpper:`|s|* p i (y-x)+`|s-c|* p i x<r by nra.
exact:le_lt_trans hT hUpper.
Qed.

(** Source for [seminorm_family_vector_topology]: the defining
    seminorm topology is a topological vector space, supporting
    Federer 4.1.1, p. 344. *)
Theorem seminorm_family_vector_topology : is_open_vector_topology O.
Proof.
constructor; [exact:hO.1|exact:seminorm_family_addition_continuous|
  exact:seminorm_family_scaling_continuous].
Qed.

(** Source for [seminorm_family_locally_convex]: convex balls
    give local convexity, supporting Federer 4.1.1, p. 344. *)
Theorem seminorm_family_locally_convex : open_family_locally_convex O.
Proof.
move=>A hA.
have [i [r [hr hb]]]:=(seminorm_family_neighbourhood_basis hp hO 0 A).1 hA.
exists [set x|p i (x-0)<r]; split.
- apply:(seminorm_family_neighbourhood_basis hp hO 0 _).2.
  exists i,r; split=>//.
- split; first exact hb.
  move=>x y hx hy t ht ht1.
  change (is_true (p i (x-0)<r)) in hx.
  change (is_true (p i (y-0)<r)) in hy.
  change (is_true (p i (((1-t)*:x+t*:y)-0)<r)).
  rewrite !subr0 in hx hy *.
  exact:(@seminorm_family_convex_ball R E I p hp i r x y t ht ht1 hx hy).
Qed.
End SeminormVectorTopology.
