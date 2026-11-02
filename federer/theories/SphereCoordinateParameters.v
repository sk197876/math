(** Federer (1969), 3.2.13, p. 251: specialize the
    angular parameters to ((t+1)/2,1/2,...,1/2), with any
    distinguished coordinate and every real t>-1. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import EulerGamma EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [sphere_coordinate_parameters]: the parameter
    specialization giving the coordinate moment in Federer 3.2.13,
    p. 251; the first coordinate may be replaced by any coordinate. *)
Definition sphere_coordinate_parameters (R:realType) m (i:'I_m) (t:R) (j:'I_m):R:=
  if j==i then (t+1)/2 else 1/2.

(** Source for [positive_coordinate_moment_parameter]: positivity
    of (t+1)/2 for the full printed range t>-1,
    Federer 3.2.13, p. 251. *)
Lemma positive_coordinate_moment_parameter (R:realType) (t:R):
  -1<t ->0<(t+1)/2.
Proof. move=>ht; apply:divr_gt0; lra. Qed.

(** Source for [sphere_coordinate_parameters_positive]: all
    specialized angular parameters are positive for t>-1,
    Federer 3.2.13, p. 251. *)
Lemma sphere_coordinate_parameters_positive (R:realType) m (i:'I_m) (t:R):
  -1<t ->forall j,0<sphere_coordinate_parameters i t j.
Proof.
move=>ht j; rewrite /sphere_coordinate_parameters; case:ifP=>h.
- exact:positive_coordinate_moment_parameter ht.
- exact:positive_real_half.
Qed.

(** Source for [sphere_coordinate_parameter_sum]: the parameter
    sum in the coordinate moment is (t+m)/2,
    Federer 3.2.13, p. 251. *)
Lemma sphere_coordinate_parameter_sum (R:realType) m (i:'I_m) (t:R):
  (0<m)%N ->(\sum_j sphere_coordinate_parameters i t j)=(t+m%:R)/2.
Proof.
move=>hm.
rewrite (bigD1 i) //= /sphere_coordinate_parameters eqxx.
have hRest:(\sum_(j | j!=i) (if j==i then (t+1)/2 else 1/2))=
    \sum_(j:'I_m | j!=i) (1/2:R).
  apply:eq_bigr=>j hj; by rewrite (negbTE hj).
rewrite hRest sumr_const cardC1 card_ord -subn1 -(mulr_natl (1/2:R) (m-1)).
have hNat:(m-1+1=m)%N:=subnK hm.
have hCast:=congr1 (fun k:nat=>(k%:R:R)) hNat; rewrite natrD in hCast.
have hPred:((m-1)%:R:R)=m%:R-1 by lra.
rewrite hPred; field; lra.
Qed.
