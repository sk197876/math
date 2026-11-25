(** Federer (1969), 3.2.7, p. 246: supporting
    geometry of positive oscillation intervals. Their
    reciprocal phases give pairwise disjoint closed
    intervals in (0,1], with a uniform reciprocal-index
    lower bound for the peak parameters. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring.
From Federer Require Import RealTrigonometryUP RealTrigonometrySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Geometry.
Variable R:realType.
Local Notation p:=(@RealTrigonometry.half_period R).

(** Source for [oscillation_zero_parameter]: reciprocal
    phase of a sine zero in the third example
    of Federer 3.2.7, p. 246. *)
Definition oscillation_zero_parameter (L k:nat):R:=(2*(L+k)%:R * p)^-1.

(** Source for [oscillation_peak_parameter]: reciprocal
    phase of a positive sine peak in the third
    example of Federer 3.2.7, p. 246. *)
Definition oscillation_peak_parameter (L k:nat):R:=(2*(L+k)%:R * p+p/2)^-1.

(** Source for [oscillation_crossing_constant]: positive
    reciprocal-index constant for the peak parameters,
    supporting Federer 3.2.7, p. 246. *)
Definition oscillation_crossing_constant (L:nat):R:=(2 * p+(2*L%:R * p+p/2))^-1.

(** Source for [oscillation_cycle_offset_exists]: discard
    finitely many large parameters so all remaining
    cycles lie in the printed interval [0,1],
    supporting Federer 3.2.7, p. 246. *)
Lemma oscillation_cycle_offset_exists:
  exists L:nat,(0<L)%N /\ 1<=2*L%:R * p.
Proof.
have hp:0<p:=real_trigonometry_pi_positive (@RealTrigonometry.laws R).
pose L:=Num.bound (p^-1+1).
have hInv:0<p^-1 by rewrite invr_gt0.
have hPos:0<=p^-1+1 by lra.
have hL:p^-1+1<L%:R:=archi_boundP hPos.
have hNat:(0<L)%N.
  have hh:(0:R)<L%:R by lra.
  by move:hh; rewrite ltr0n.
exists L; split=>//.
have hMul:(p^-1+1) * p<L%:R * p by rewrite ltr_pM2r.
rewrite mulrDl mulVf ?gt_eqF // mul1r in hMul.
have hLP:0<=L%:R * p by apply:mulr_ge0; [exact:ler0n|exact:ltW hp].
nra.
Qed.

(** Source for [oscillation_cycle_parameter_bounds]: each
    selected closed crossing interval lies in (0,1],
    supporting Federer 3.2.7, p. 246. *)
Lemma oscillation_cycle_parameter_bounds L k:
  1<=2*L%:R * p ->
  0<oscillation_peak_parameter L k /\
  oscillation_peak_parameter L k<oscillation_zero_parameter L k /\
  oscillation_zero_parameter L k<= 1.
Proof.
move=>hL; have hp:0<p:=real_trigonometry_pi_positive (@RealTrigonometry.laws R).
have hk:(0:R)<=k%:R:=ler0n R k.
have hPhase:1<=2*(L+k)%:R * p by rewrite natrD; nra.
have hz:0<2*(L+k)%:R * p by lra.
have hp2:0<p/2 by rewrite divr_gt0 // ltr0n.
split; first by rewrite /oscillation_peak_parameter invr_gt0; lra.
split.
- have hPeak:0<2*(L+k)%:R * p+p/2 by lra.
  rewrite /oscillation_peak_parameter /oscillation_zero_parameter (@ltf_pV2 R _ _ hPeak hz); lra.
- rewrite /oscillation_zero_parameter invf_le1 //; exact hPhase.
Qed.

(** Source for [oscillation_cycle_parameters_separated]:
    a later zero parameter is strictly below
    an earlier peak, so the closed intervals
    are disjoint, supporting Federer 3.2.7, p. 246. *)
Lemma oscillation_cycle_parameters_separated L i j:
  1<=2*L%:R * p -> (i<j)%N ->
  oscillation_zero_parameter L j<oscillation_peak_parameter L i.
Proof.
move=>hL hij; have hp:0<p:=real_trigonometry_pi_positive (@RealTrigonometry.laws R).
have hIJ0:(i.+1%:R:R)<=j%:R by rewrite ler_nat.
have hIJ:(i%:R:R)+1<=j%:R by move:hIJ0; rewrite -[i.+1]addn1 natrD.
have hi:(0:R)<=i%:R:=ler0n R i.
have hj:(0:R)<=j%:R:=ler0n R j.
have hz:0<2*(L+j)%:R * p by rewrite natrD; nra.
have hP2:0<p/2 by rewrite divr_gt0 // ltr0n.
have hPeak:0<2*(L+i)%:R * p+p/2.
  rewrite natrD; nra.
rewrite /oscillation_zero_parameter /oscillation_peak_parameter (@ltf_pV2 R _ _ hz hPeak).
rewrite !natrD; have hHalf:p/2<p by rewrite ltr_pdivrMr ?ltr0n //; lra.
nra.
Qed.

(** Source for [oscillation_crossing_constant_bounds]:
    the reciprocal-index constant is in (0,1],
    supporting the small target intervals in
    Federer 3.2.7, p. 246. *)
Lemma oscillation_crossing_constant_bounds L:
  1<=2*L%:R * p -> 0<oscillation_crossing_constant L<= 1.
Proof.
move=>hL; have hp:0<p:=real_trigonometry_pi_positive (@RealTrigonometry.laws R).
have hp2:0<p/2 by rewrite divr_gt0 // ltr0n.
have hDen:1<=2 * p+(2*L%:R * p+p/2) by lra.
have hPos:0<2 * p+(2*L%:R * p+p/2) by lra.
rewrite /oscillation_crossing_constant; apply/andP; split.
- by rewrite invr_gt0.
- by rewrite invf_le1.
Qed.

(** Source for [oscillation_peak_reciprocal_index_bound]:
    the first n peak parameters are at least
    c/n, supporting the divergent weighted level
    count in Federer 3.2.7, p. 246. *)
Lemma oscillation_peak_reciprocal_index_bound L n i:
  1<=2*L%:R * p -> (0<n)%N -> (i<n)%N ->
  oscillation_crossing_constant L/n%:R<=oscillation_peak_parameter L i.
Proof.
move=>hL hn hin; have hp:0<p:=real_trigonometry_pi_positive (@RealTrigonometry.laws R).
have hN:(0:R)<n%:R by rewrite ltr0n.
have hN1:(1:R)<=n%:R by rewrite ler1n.
have hI:(0:R)<=i%:R:=ler0n R i.
have hIN:(i%:R:R)<n%:R by rewrite ltr_nat.
have hP2:0<p/2 by rewrite divr_gt0 // ltr0n.
have hD:0<2 * p+(2*L%:R * p+p/2) by lra.
have hPhase:0<2*(L+i)%:R * p+p/2 by rewrite natrD; nra.
have hBase:0<=2*L%:R * p+p/2 by lra.
have hMul:=ler_wpM2l hBase hN1; rewrite mulr1 in hMul.
have hBound:2*(L+i)%:R * p+p/2<=(2 * p+(2*L%:R * p+p/2))*n%:R.
  rewrite natrD; nra.
have hProd:0<n%:R*(2 * p+(2*L%:R * p+p/2)) by rewrite mulr_gt0.
have hBound':2*(L+i)%:R * p+p/2<=n%:R*(2 * p+(2*L%:R * p+p/2)).
  by rewrite [leRHS]mulrC.
have hInverse: (n%:R*(2 * p+(2*L%:R * p+p/2)))^-1<=
    (2*(L+i)%:R * p+p/2)^-1.
  by rewrite (@lef_pV2 R _ _ hProd hPhase).
rewrite /oscillation_crossing_constant /oscillation_peak_parameter -invrM.
exact hInverse.
  by rewrite unitfE (gt_eqF hN).
by rewrite unitfE (gt_eqF hD).
Qed.
End Geometry.
