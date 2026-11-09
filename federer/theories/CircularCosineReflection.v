(** Federer (1969), 3.3.19, p. 302: scalar
    cyclic symmetry and monotonicity for the exact minimum
    distance of the original circular child centres. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Reflection.
Variable R:realType.
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_cosine_full_period]: scalar cyclic
    symmetry of the actual child centres, 3.3.19, p. 302. *)
Lemma circular_cosine_full_period x:C (x+(p+p))=C x.
Proof. by rewrite addrA !(real_cosine_half_period hb) opprK. Qed.

(** Source for [circular_cosine_reflected_period]: scalar
    reflection around the full period in the original
    cyclic geometry of 3.3.19, p. 302. *)
Lemma circular_cosine_reflected_period x:C (2* p-x)=C x.
Proof.
have hEq:2* p-x=(-x)+(p+p) by ring.
by rewrite hEq circular_cosine_full_period (circular_trig_cosine_even ht).
Qed.

(** Source for [circular_cosine_weak_decrease]: weak endpoint
    version of the proved elementary cosine order law,
    supporting centre separation in 3.3.19, p. 302. *)
Lemma circular_cosine_weak_decrease a b:
  0<=a ->a<=b ->b<=p ->C b<=C a.
Proof.
move=>ha hab hbp;case:(eqVneq a b)=>[->|hne];first exact:lexx.
have hap:a<=p:=le_trans hab hbp.
have hb0:0<=b:=le_trans ha hab.
have habS:a<b by rewrite lt_neqAle hne hab.
exact:(ltW (@circular_trig_cosine_decreases R S C (@CircularTrigonometry.arcsine R)
  (@CircularTrigonometry.arccosine R) p ht a b ha hap hb0 hbp habS)).
Qed.

(** Source for [circular_cosine_between_symmetric_endpoints]:
    the smallest cyclic angular spacing controls every
    original distinct pair, supporting the exact minimum
    centre distance in 3.3.19, p. 302. The angular
    interval crosses the opposite point; reflection handles
    its second half using only public scalar laws. *)
Lemma circular_cosine_between_symmetric_endpoints a x:
  0<=a ->a<=p ->a<=x ->x<=2* p-a ->C x<=C a.
Proof.
move=>ha hap hax hxa;case:(leP x p)=>hxp.
- exact:circular_cosine_weak_decrease ha hax hxp.
- have he0:0<=2* p-x by lra.
  have hae:a<=2* p-x by lra.
  have hep:2* p-x<=p by lra.
  rewrite -(circular_cosine_reflected_period x).
  exact:circular_cosine_weak_decrease ha hae hep.
Qed.
End Reflection.
