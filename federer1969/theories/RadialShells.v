(** Federer (1969), 2.10.20, pp. 181–182: closed radial shells of width t
    greater than the fixed diameter cutoff. Same-parity shells are separated
    by at least t. The working Federer erratum has no entry for book pp.
    181–182. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology ring lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_radial_shell]: direct radial factor
    of B_j in the proof of 2.10.20, p. 181,
    with j=n+1. Intersection with the target A is
    taken separately. Both boundary spheres are retained. *)
Definition metric_radial_shell (R : realType) (X : metricType R) (a : X) (t : R) n : set X :=
  [set x | (n%:R*t<=mdist a x<=n.+1%:R*t)%R].

(** Source for [metric_radial_shells_cover]: supporting
    coverage by the shells B_j in 2.10.20,
    pp. 181–182. The ordinary scalar integer part
    supplies a witness; no geometric choice is exposed. *)
Lemma metric_radial_shells_cover (R : realType) (X : metricType R) (a : X) (t : R) :
  0<t -> forall x : X, exists n, metric_radial_shell a t n x.
Proof.
move=> ht x.
pose q := mdist a x/t.
have hdist : 0<=mdist a x by exact: mdist_ge0.
have hq : 0<=q := divr_ge0 hdist (ltW ht).
have /andP[hl hu] := truncn_itv hq.
exists (Num.truncn q); apply/andP; split.
- by move: hl; rewrite /q ler_pdivlMr.
- apply: ltW; by move: hu; rewrite /q ltr_pdivrMr.
Qed.

(** Source for [metric_radial_shell_parity_separated]: supporting
    same-parity distance bound in 2.10.20, p. 182.
    Indices 2k+p and 2N+p with k<N have a full
    shell width between them. The natural offset p
    includes both parities without a parity case split. *)
Lemma metric_radial_shell_parity_separated (R : realType) (X : metricType R)
    (a : X) (t : R) (p k N : nat) :
  0<t -> (k<N)%N -> forall x, metric_radial_shell a t (k.*2+p)%N x ->
    forall y, metric_radial_shell a t (N.*2+p)%N y -> t<=mdist x y.
Proof.
move=> ht hk x /andP[hxl hxu] y /andP[hyl hyu].
have hkn : ((k.+1).*2+p<=N.*2+p)%N by rewrite leq_add2r leq_double.
have hmul : (((k.+1).*2+p)%:R : R)*t<=(N.*2+p)%:R*t.
  by rewrite ler_pM2r // ler_nat.
have he : (((k.*2+p).+1)%:R : R)*t+t=(((k.+1).*2+p)%:R : R)*t.
  have hs (n : nat) : (n.+1%:R : R)=n%:R+1 by rewrite -natr1.
  have hj : ((k.+1).*2+p=(k.*2+p).+2)%N by rewrite doubleS !addSn.
  rewrite hj (hs (k.*2+p).+1) !(hs (k.*2+p)%N); ring.
rewrite -he in hmul.
have hstep := le_trans (lerD hxu (lexx t)) (le_trans hmul hyl).
have htri := metric_triangle a x y.
lra.
Qed.
