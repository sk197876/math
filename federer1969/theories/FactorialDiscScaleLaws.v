(** Federer (1969), 3.3.19, p. 302: exact factorial
    counts, conserved radius sum and shrinking mesh derived
    solely from the independently specified recursions. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import FactorialDiscScalesUP ArchimedeanReciprocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Scales.
Variable R:realType.
Variables (N:nat->nat) (rho:nat->R).
Hypothesis h:is_factorial_disc_scales N rho.

(** Source for [factorial_disc_count_positive]: every level
    has a positive count, supporting 3.3.19, p. 302. *)
Lemma factorial_disc_count_positive j:(0<N j)%N.
Proof.
elim:j=>[|j ih]; first by rewrite (factorial_disc_count_root h).
by rewrite (factorial_disc_count_step h) muln_gt0 ih andbT addn_gt0 orbT.
Qed.

(** Source for [factorial_disc_count_factorial]: the literal
    count n!/3! on p. 302, with book n=j+3. *)
Lemma factorial_disc_count_factorial j:(N j*6=(j+3)`!)%N.
Proof.
elim:j=>[|j ih]; first by rewrite (factorial_disc_count_root h).
rewrite (factorial_disc_count_step h) -mulnA ih addSn factS.
by rewrite -addnS.
Qed.

(** Source for [factorial_disc_count_radius]: the conserved
    sum of radii one in 3.3.19, p. 302, prior to
    proving that the actual discs have these counts. *)
Lemma factorial_disc_count_radius j:(N j)%:R*rho j= 1.
Proof.
elim:j=>[|j ih]; first by rewrite (factorial_disc_count_root h) (factorial_disc_radius_root h) mul1r.
have hn:((j+4)%:R:R)!= 0 by rewrite pnatr_eq0 addn_eq0 andbF.
rewrite (factorial_disc_count_step h) (factorial_disc_radius_step h) natrM.
transitivity ((N j)%:R*(rho j/(j+4)%:R*(j+4)%:R));first by ring.
by rewrite divfK.
Qed.

(** Source for [factorial_disc_radius_inverse]: positive
    reciprocal count expression for rho_n, 3.3.19, p. 302. *)
Lemma factorial_disc_radius_inverse j:rho j=(N j)%:R^-1.
Proof.
have hn:((N j)%:R:R)!= 0 by rewrite pnatr_eq0 -lt0n factorial_disc_count_positive.
have hh:=congr1 (fun z:R=>(N j)%:R^-1*z) (factorial_disc_count_radius j).
by rewrite mulrA mulVf // mul1r mulr1 in hh.
Qed.

(** Source for [factorial_disc_radius_positive]: every
    original radius is positive, 3.3.19, p. 302. *)
Lemma factorial_disc_radius_positive j:0<rho j.
Proof. by rewrite factorial_disc_radius_inverse invr_gt0 ltr0n factorial_disc_count_positive. Qed.

(** Source for [factorial_disc_radius_factorial]: the exact
    formula rho_n= 3!/n! in 3.3.19, p. 302. *)
Lemma factorial_disc_radius_factorial j:rho j= 6/((j+3)`!)%:R.
Proof.
rewrite -(factorial_disc_count_factorial j) natrM invfM factorial_disc_radius_inverse.
have h6:((6:R)!= 0) by rewrite pnatr_eq0.
by rewrite mulrCA divff // mulr1.
Qed.

(** Source for [factorial_disc_count_grows]: elementary
    unboundedness needed for the mesh of 3.3.19, p. 302. *)
Lemma factorial_disc_count_grows j:(j.+1<=N j)%N.
Proof.
elim:j=>[|j ih]; first by rewrite (factorial_disc_count_root h).
rewrite (factorial_disc_count_step h).
have hTwo:(2<=j+4)%N:=leq_trans (erefl true : (2<=4)%N) (leq_addl j 4).
have hMul:(2*N j<=(j+4)*N j)%N by rewrite leq_mul2r hTwo orbT.
have hPos:=factorial_disc_count_positive j.
have hNext:((N j).+1<=2*N j)%N.
  by rewrite mul2n -addnn -addn1 leq_add2l.
exact:leq_trans (leq_trans (leq_ltn_trans ih (ltnSn _)) hNext) hMul.
Qed.

(** Source for [factorial_disc_radius_decreases]: strict
    mesh decrease at every subdivision, 3.3.19, p. 302. *)
Lemma factorial_disc_radius_decreases j:rho j.+1<rho j.
Proof.
have hp:=factorial_disc_radius_positive j.
have hn:(0<(j+4)%:R:>R) by rewrite ltr0n addn_gt0 orbT.
have hn1:(1<(j+4)%:R:>R).
  rewrite ltr1n;exact:leq_trans (erefl true : (2<=4)%N) (leq_addl j 4).
have hScaled:rho j<rho j*(j+4)%:R.
  by rewrite -{1}[rho j]mulr1 ltr_pM2l.
by rewrite (factorial_disc_radius_step h) ltr_pdivrMr.

Qed.

(** Source for [factorial_disc_radius_small]: the original
    radii tend to zero, as used in all arbitrarily fine
    covers and density arguments of 3.3.19, pp. 302–306. *)
Lemma factorial_disc_radius_small e:0<e ->exists J,forall j,(J<=j)%N ->rho j<e.
Proof.
move=>he;have [J hJ]:=real_reciprocal_below he;exists J=>j hj.
have hSucc:(J.+1<=j.+1)%N by rewrite ltnS.
have hCount:(J.+1<=N j)%N:=leq_trans hSucc (factorial_disc_count_grows j).
have hN:(0<(N j)%:R:>R) by rewrite ltr0n factorial_disc_count_positive.
have hJp:(0<J.+1%:R:>R) by rewrite ltr0n.
have hInv:((N j)%:R:R)^-1<=(J.+1%:R:R)^-1 by rewrite lef_pV2 // ler_nat.
rewrite factorial_disc_radius_inverse;exact:le_lt_trans hInv hJ.
Qed.
End Scales.
