(** Federer 2.10.45, pp. 202-203: the two coefficient endpoints for
    a Euclidean factor of natural dimension m and an arbitrary real
    section degree k>=0. Use the actual Gamma-normalized diameter
    coefficients; powers of two cancel in the section ratio. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import RealHausdorffNormalisation RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_euclidean_product_upper_coefficient]: the printed
    xi in Federer 2.10.45, p. 202, in diameter-coefficient form.
    The factor sqrt(m+1)^(k+m) uses the actual real power. *)
Definition real_euclidean_product_upper_coefficient (R : realType) (m : nat)
    (k : R) (hk : 0 <= k) : R :=
  real_hausdorff_normalisation (addr_ge0 hk (ler0n R m))/real_hausdorff_normalisation hk*
    real_power (Num.sqrt m.+1%:R) (k+m%:R).

(** Source for [real_euclidean_product_upper_coefficient_positive]:
    supporting positivity for Federer 2.10.45, pp. 202-203, including
    zero Euclidean dimension and zero real section degree. *)
Lemma real_euclidean_product_upper_coefficient_positive (R : realType) m
    (k : R) (hk : 0 <= k) : 0 < real_euclidean_product_upper_coefficient m hk.
Proof.
rewrite /real_euclidean_product_upper_coefficient; apply: mulr_gt0.
- exact: divr_gt0 (real_hausdorff_normalisation_positive _) (real_hausdorff_normalisation_positive hk).
- apply: real_power_strictly_positive; by rewrite sqrtr_gt0 ltr0n.
Qed.

(** Source for [real_euclidean_product_coefficient_cost_identity]:
    supporting cancellation in the final double sum of Federer 2.10.45,
    p. 203. The original Gamma coefficient is retained exactly. *)
Lemma real_euclidean_product_coefficient_cost_identity (R : realType) m
    (k : R) (hk : 0 <= k) :
  real_euclidean_product_upper_coefficient m hk*real_hausdorff_normalisation hk =
  real_hausdorff_normalisation (addr_ge0 hk (ler0n R m))*
    real_power (Num.sqrt m.+1%:R) (k+m%:R).
Proof.
rewrite /real_euclidean_product_upper_coefficient mulrAC divfK //.
exact: lt0r_neq0 (real_hausdorff_normalisation_positive hk).
Qed.

(** Source for [real_euclidean_product_lower_coefficient]: the lower
    endpoint for c in Federer 2.10.45, p. 202. Its equivalent printed
    form is c alpha(k)/alpha(k+m)>=1/alpha(m). *)
Definition real_euclidean_product_lower_coefficient (R : realType) (m : nat)
    (k : R) (hk : 0 <= k) : R :=
  real_hausdorff_normalisation (addr_ge0 hk (ler0n R m))/
    (real_hausdorff_normalisation hk*real_hausdorff_normalisation (ler0n R m)).

(** Source for [real_euclidean_product_lower_coefficient_positive]:
    supporting positivity of the lower endpoint in Federer 2.10.45,
    pp. 202-203, from the actual positive Gamma normalizers. *)
Lemma real_euclidean_product_lower_coefficient_positive (R : realType) m
    (k : R) (hk : 0 <= k) : 0 < real_euclidean_product_lower_coefficient m hk.
Proof.
rewrite /real_euclidean_product_lower_coefficient; apply: divr_gt0;
  first exact: real_hausdorff_normalisation_positive.
exact: mulr_gt0 (real_hausdorff_normalisation_positive hk)
  (real_hausdorff_normalisation_positive (ler0n R m)).
Qed.
