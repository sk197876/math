(** Federer (1969), 3.3.19, p. 302: local
    representatives of the actual original cyclic angles
    in a closed semicircle-centred period interval. Only
    an auxiliary scalar cut is used; original directions
    remain unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularUnitVectors CircularCosineReflection CyclicGridShiftSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Lifts.
Variable R:realType.
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_angle_central_representative]:
    an original angle in [0,2pi] has a locally
    equal-direction representative in [pi,3pi], supporting
    the halfplane count in 3.3.19, p. 302. *)
Lemma circular_angle_central_representative (t:R):0<=t ->t<=2* p ->
  exists u:R,p<=u /\u<=3* p /\circular_unit_vector u=circular_unit_vector t.
Proof.
move=>ht0 ht2;have hp:=real_trigonometry_pi_positive hb.
case:(leP p t)=>hpt.
- exists t;split=>//;split=>//;by lra.
- exists (t+(p+p));split;first by lra.
  split;first by lra.
  exact:circular_unit_vector_period.
Qed.

(** Source for [circular_angle_lift_branch]: exact local
    crossing test for the original angular cut at u-pi,
    supporting 3.3.19, p. 302. *)
Definition circular_angle_lift_branch n (u:R) (k:'I_n):bool:=
  (2* p/n%:R)* k%:R<u-p.

(** Source for [circular_angle_lift_bounds]: actual
    lifted cyclic angles lie in [u-pi,u+pi],
    supporting every orientation of the original halfplane
    count in 3.3.19, p. 302. Both sides of
    the period cut are proved from the index bounds. *)
Lemma circular_angle_lift_bounds n (u:R) (k:'I_n):
  (0<n)%N ->p<=u ->u<=3* p ->
  let t:=cyclic_grid_shifted_point (2* p/n%:R) (circular_angle_lift_branch u) k in
  -p<=t-u /\t-u<=p.
Proof.
move=>hn hpu hup /=.
have hp:=real_trigonometry_pi_positive hb.
have hNP:(0<n%:R:>R) by rewrite ltr0n.
have hNN:(n%:R:R)!= 0 by rewrite gt_eqF.
pose q:R:=2* p/n%:R.
have hQ:0<q by rewrite /q divr_gt0 // mulr_gt0 // ltr0n.
have hBudget:q* n%:R= 2* p by rewrite /q divfK.
have hk0:(0<=k%:R:>R) by rewrite ler0n.
have hkN:(k%:R<n%:R:>R) by rewrite ltr_nat;exact:ltn_ord.
have hLower:0<=q* k%:R by nra.
have hUpper:q* k%:R<2* p by nra.
rewrite /cyclic_grid_shifted_point /circular_angle_lift_branch -/q.
case:(ltP (q* k%:R) (u-p))=>hCut /=;split;nra.
Qed.

(** Source for [circular_angle_lift_cosine]: lifting the
    actual cyclic angle across its local cut leaves
    its original directional dot product unchanged,
    supporting 3.3.19, p. 302. *)
Lemma circular_angle_lift_cosine n (u:R) (k:'I_n):(0<n)%N ->
  C (cyclic_grid_shifted_point (2* p/n%:R) (circular_angle_lift_branch u) k-u)=
    C (2* p* k%:R/n%:R-u).
Proof.
move=>hn;have hNN:(n%:R:R)!= 0 by rewrite pnatr_eq0 -lt0n.
pose q:R:=2* p/n%:R.
have hBudget:q* n%:R= 2* p by rewrite /q divfK.
have hAngle:2* p* k%:R/n%:R=q* k%:R by rewrite /q;ring.
rewrite hAngle /cyclic_grid_shifted_point -/q.
case:(circular_angle_lift_branch u k)=>/=;last by rewrite addr0.
have hEq:q*(k%:R+n%:R)-u=(q* k%:R-u)+(p+p) by rewrite mulrDr hBudget;ring.
by rewrite hEq circular_cosine_full_period.
Qed.
End Lifts.
