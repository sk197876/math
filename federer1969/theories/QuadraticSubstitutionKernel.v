(** Federer (1969), 3.4.5, p. 321: finite
    monomial coefficients for y^2=-x^2+lambda*x^3,
    supporting the actual axis remainder argument. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ShiftedAffinePowerCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Kernel.
Variable K:fieldType.

(** Source for [quadratic_substitution_kernel]: the coefficient
    of x^N after replacing x^i*y^(2k+parity) by
    x^(i+2k+parity)*(-1+lambda*x)^k, supporting the finite
    remainder in 3.4.5, p. 321. *)
Definition quadratic_substitution_kernel (parity:nat) (lambda:K) (N i k:nat):K:=
  shifted_affine_power_coefficient (i+2*k+parity)%N k lambda N.

(** Source for [quadratic_substitution_kernel_below]: a monomial
    above the original total order contributes no coefficient,
    supporting 3.4.5, p. 321. *)
Lemma quadratic_substitution_kernel_below parity lambda N i k:
  (N<i+2*k+parity)%N ->quadratic_substitution_kernel parity lambda N i k=0.
Proof. exact:(@shifted_affine_power_coefficient_below K (i+2*k+parity)%N k lambda N). Qed.

(** Source for [quadratic_substitution_kernel_first_cutoff]: the
    original finite x cutoff needs no coefficient from
    higher x orders, supporting 3.4.5, p. 321. *)
Lemma quadratic_substitution_kernel_first_cutoff parity lambda N i k:
  (N<i)%N ->quadratic_substitution_kernel parity lambda N i k=0.
Proof.
move=>hI;apply:quadratic_substitution_kernel_below.
exact:(leq_trans hI (leq_trans (leq_addr (2*k)%N i) (leq_addr parity (i+2*k)%N))).
Qed.

(** Source for [quadratic_substitution_kernel_second_cutoff]: the
    original finite y cutoff needs no coefficient from
    higher paired y orders, supporting 3.4.5, p. 321. *)
Lemma quadratic_substitution_kernel_second_cutoff parity lambda N i k:
  (N<k)%N ->quadratic_substitution_kernel parity lambda N i k=0.
Proof.
move=>hK;apply:quadratic_substitution_kernel_below.
have hDouble:(k<=2*k)%N by rewrite mul2n -addnn;exact:leq_addr.
have hBound:(k<= i+2*k+parity)%N:=leq_trans hDouble
  (leq_trans (leq_addl i (2*k)%N) (leq_addr parity (i+2*k)%N)).
exact:(leq_trans hK hBound).
Qed.

(** Source for [quadratic_substitution_kernel_successor]: multiplication
    by the original y^2 relation is exactly the
    difference of its quadratic and cubic x shifts,
    supporting 3.4.5, p. 321. It follows from
    actual finite polynomial equality and coefficient uniqueness. *)
Theorem quadratic_substitution_kernel_successor (h0:[pchar K] =i pred0) parity lambda N i k:
  quadratic_substitution_kernel parity lambda N i k.+1=
    lambda*quadratic_substitution_kernel parity lambda N (i+3)%N k-
    quadratic_substitution_kernel parity lambda N (i+2)%N k.
Proof.
have hShift (d:nat):(i+d+2*k+parity= i+2*k+parity+d)%N.
  by rewrite [(i+d+2*k)%N]addnAC [(i+2*k+d+parity)%N]addnAC.
have hIndex:(i+2*k.+1+parity= i+2*k+parity+2)%N.
  by rewrite mulnS addnA [(i+2+2*k)%N]addnAC [(i+2*k+2+parity)%N]addnAC.
rewrite /quadratic_substitution_kernel hIndex (hShift 2%N) (hShift 3%N)
  (@shifted_affine_power_coefficient_successor K h0 (i+2*k+parity+2)%N k lambda N).
by rewrite !addnS !addn0.
Qed.
End Kernel.
