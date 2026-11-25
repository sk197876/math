(** Federer (1969), 4.1.11, p. 365: the exact
    coefficient i!j!/(i+j+1)! in the join mass estimate.
    These arithmetic laws support its original time integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ScalarBetaCoefficient.
Variable R:realType.

(** Source for [scalar_beta_coefficient]: the printed
    factorial coefficient, Federer 4.1.11, p. 365. *)
Definition scalar_beta_coefficient i j:R:=
  (i`!)%:R*(j`!)%:R/(((i+j).+1)`!)%:R.

(** Source for [scalar_beta_coefficient_positive]: the
    printed coefficient is strictly positive in every
    natural pair of degrees, supporting Federer 4.1.11,
    p. 365, including both zero endpoints. *)
Lemma scalar_beta_coefficient_positive i j:0<scalar_beta_coefficient i j.
Proof.
rewrite /scalar_beta_coefficient divr_gt0 //;last by rewrite ltr0n fact_gt0.
by rewrite mulr_gt0 // ltr0n fact_gt0.
Qed.

(** Source for [scalar_beta_coefficient_zero]: the
    degree-zero endpoint is 1/(j+1), supporting the
    original time integral in Federer 4.1.11, p. 365. *)
Lemma scalar_beta_coefficient_zero j:scalar_beta_coefficient 0%N j=(j.+1%:R:R)^-1.
Proof.
have hFact:((j`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
by rewrite /scalar_beta_coefficient add0n fact0 mul1r factS natrM invfM
  mulrA mulrAC mulfV // mul1r.
Qed.

(** Source for [scalar_beta_coefficient_successor]: the
    factorial recurrence used to integrate (1-t)^i t^j,
    supporting Federer 4.1.11, p. 365. *)
Lemma scalar_beta_coefficient_successor i j:
  scalar_beta_coefficient i.+1 j=
    (i.+1%:R/j.+1%:R)*scalar_beta_coefficient i j.+1.
Proof.
have hJ:(j.+1%:R:R)!=0 by rewrite pnatr_eq0.
have hDegree:(i.+1+j).+1=(i+j.+1).+1 by rewrite addSn addnS.
rewrite /scalar_beta_coefficient hDegree [i.+1`!]factS [j.+1`!]factS !natrM.
have hReorder:(i.+1%:R/j.+1%:R)*((i`!)%:R*(j.+1%:R*(j`!)%:R)/(((i+j.+1).+1)`!)%:R)=
    ((i.+1%:R*(i`!)%:R)*(j`!)%:R/(((i+j.+1).+1)`!)%:R)*((j.+1%:R:R)^-1*j.+1%:R) by ring.
rewrite !natrM in hReorder.
by rewrite hReorder mulVf // mulr1.
Qed.
End ScalarBetaCoefficient.
