(** Federer (1969), 3.2.13, p. 251: positive half-integer
    parameters in the sphere and projection-constant formulas. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra.
From Federer Require Import EulerGamma.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_real_half]: positivity of 1/2 in the
    Gamma formulas of Federer 3.2.13, p. 251. *)
Lemma positive_real_half (R:realType):0<(1/2:R).
Proof. by apply:divr_gt0; lra. Qed.

(** Source for [positive_dimension_half]: positivity of m/2 for
    the nonempty spheres in Federer 3.2.13, p. 251. *)
Lemma positive_dimension_half (R:realType) m:
  (0<m)%N ->0<(m%:R:R)/2.
Proof.
move=>hm; have hM:0<(m%:R:R) by rewrite ltr0n.
apply:divr_gt0=>//; lra.
Qed.

(** Source for [euler_gamma_half]: the common Gamma(1/2)
    constant in Federer 3.2.13, p. 251, using the actual
    finite defining integral rather than a new normalization. *)
Definition euler_gamma_half (R:realType):R:=euler_gamma (positive_real_half R).

(** Source for [euler_gamma_proof_irrelevant]: bookkeeping for
    repeated Gamma values at the same positive parameter in
    Federer 3.2.13, pp. 250–251. *)
Lemma euler_gamma_proof_irrelevant (R:realType) (s:R) (h1 h2:0<s):
  euler_gamma h1=euler_gamma h2.
Proof. by have ->:h1=h2:=Prop_irrelevance _ _. Qed.
