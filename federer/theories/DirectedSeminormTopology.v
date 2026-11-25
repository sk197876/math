(** Federer (1969), 4.1.1, p. 344: consequences of the seminorm
    neighbourhood specification. Proofs use the public abstract laws,
    without unfolding the construction or its opaque witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import RealNormUP OpenFamilyTopologyUP DirectedSeminormFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SeminormTopologyLaws.
Variable R : realType.
Variable E : lmodType R.
Variable I : Type.
Variable p : I -> E -> R.
Variable O : set (set E).
Hypothesis hp : is_directed_seminorm_family p.
Hypothesis hO : is_seminorm_family_topology p O.

(** Source for [seminorm_family_ball_open]: the printed seminorm
    balls are open, supporting the basic-neighbourhood assertion of
    Federer 4.1.1, p. 344. The triangle inequality supplies a smaller
    ball at each of their points. *)
Lemma seminorm_family_ball_open i a r : O [set x | p i (x-a)<r].
Proof.
apply: (hO.2 _).2=>x hx.
change (is_true (p i (x-a)<r)) in hx.
exists i,(r-p i (x-a)); split; first by rewrite subr_gt0.
move=>y hy.
have hb:=real_seminorm_triangle (directed_seminorm_laws hp i) (y-x) (x-a).
have he:(y-x)+(x-a)=y-a by rewrite addrA subrK.
rewrite he in hb.
change (is_true (p i (y-a)<r)); lra.
Qed.

(** Source for [seminorm_family_neighbourhood_basis]: exact basic
    neighbourhood criterion in Federer 4.1.1, p. 344. A single
    positive-radius ball suffices because the family is directed. *)
Theorem seminorm_family_neighbourhood_basis a A :
  open_family_neighbourhood O a A <->
  exists i r, 0<r /\ forall y, p i (y-a)<r -> A y.
Proof.
split.
- move=>[B [hB [ha hBA]]].
  have [i [r [hr hball]]]:=(hO.2 B).1 hB a ha.
  exists i,r; split=>// y hy; apply:hBA; exact:hball.
- move=>[i [r [hr hball]]].
  exists [set y|p i (y-a)<r]; split; first exact:seminorm_family_ball_open.
  split; last exact hball.
  change (is_true (p i (a-a)<r)).
  by rewrite subrr (real_seminorm_zero (directed_seminorm_laws hp i)).
Qed.

(** Source for [seminorm_family_translation_continuous]: translations
    preserve the topology in Federer 4.1.1, p. 344. The inverse
    translation has the same proof, so these maps are homeomorphisms. *)
Theorem seminorm_family_translation_continuous a :
  open_family_continuous O O (fun x=>x+a).
Proof.
move=>A hA; apply:(hO.2 _).2=>x hx.
have [i [r [hr hb]]]:=(hO.2 A).1 hA (x+a) hx.
exists i,r; split=>// y hy; apply:hb.
by rewrite opprD addrA addrAC addrK.
Qed.

(** Source for [seminorm_family_negation_continuous]: supporting
    continuity of negation for the locally convex topology of
    E(U,Y), Federer 4.1.1, p. 344. *)
Theorem seminorm_family_negation_continuous :
  open_family_continuous O O (fun x=>-x).
Proof.
move=>A hA; apply:(hO.2 _).2=>x hx.
have [i [r [hr hb]]]:=(hO.2 A).1 hA (-x) hx.
exists i,r; split=>// y hy; apply:hb.
have he:-y - -x= -(y-x) by rewrite opprB opprK addrC.
by rewrite he (real_seminorm_negate (directed_seminorm_laws hp i)).
Qed.

(** Source for [seminorm_family_convex_ball]: convexity of the
    seminorm-ball neighbourhoods in Federer 4.1.1, p. 344. This
    supplies local convexity without making it an assumed law. *)
Theorem seminorm_family_convex_ball i r (x y:E) (t:R) :
  0<=t -> t<=1 -> p i x<r -> p i y<r ->
  p i ((1-t)*:x+t*:y)<r.
Proof.
move=>ht ht1 hx hy.
have h1:0<=1-t by rewrite subr_ge0.
have hb:=real_seminorm_triangle (directed_seminorm_laws hp i) ((1-t)*:x) (t*:y).
rewrite !(real_seminorm_scale (directed_seminorm_laws hp i))
  (ger0_norm h1) (ger0_norm ht) in hb.
have he:0<(1-t)*(r-p i x)+t*(r-p i y).
  have [->|htp]:=eqVneq t 0.
  - by rewrite subr0 mul1r mul0r addr0 subr_gt0.
  - have htpos:0<t by rewrite lt_def htp ht.
    have hleft:0<=(1-t)*(r-p i x) by rewrite mulr_ge0 // subr_ge0; exact:ltW hx.
    have hright:0<t*(r-p i y) by rewrite mulr_gt0 // subr_gt0.
    by lra.
nra.
Qed.
End SeminormTopologyLaws.
