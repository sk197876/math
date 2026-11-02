(** Federer (1969), 1.10.5, p. 48: the supremum norm of a homogeneous
    polynomial function on the input unit ball. They do not supply the whole
    norm-comparison paragraph on Federer's p. 48. The supremum laws below
    apply to arbitrary functions; homogeneity is imposed in subsequent
    theorems. Extended values retain unbounded infinite-dimensional
    examples. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal.
From Federer Require Import RealNormUP ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Specification.
Variable R : realType.
Variables V W : lmodType R.
Variable NV : V -> R.
Variable NW : W -> R.

(** Source for [polynomial_unit_values]: Federer 1.10.5,
    p. 48, the set of output lengths at points of the input
    unit ball in the definition of the polynomial norm. *)
Definition polynomial_unit_values (P : V -> W) : set R :=
  fun r => exists x, NV x<=1 /\ r=NW (P x).

(** Source for [is_polynomial_norm]: Federer 1.10.5,
    p. 48, abstract supremum specification of the polynomial
    norm, permitting positive infinity. *)
Definition is_polynomial_norm (P : V -> W) (c : \bar R) : Prop :=
  is_extended_supremum (polynomial_unit_values P) c.

(** Source for [polynomial_unit_values_nonempty]: Federer
    1.10.5, p. 48, supporting nonemptiness: zero belongs to
    the unit ball even when the ambient space has dimension zero. *)
Lemma polynomial_unit_values_nonempty (hN : is_real_seminorm NV) (P : V -> W) :
  polynomial_unit_values P !=set0.
Proof.
exists (NW (P 0)); exists 0; split=> //.
by rewrite (real_seminorm_zero hN) ler01.
Qed.

(** Source for [polynomial_norm_unique]: Federer 1.10.5,
    p. 48, uniqueness of the extended value specified by
    the upper-bound and leastness laws. *)
Lemma polynomial_norm_unique (P : V -> W) c d :
  is_polynomial_norm P c -> is_polynomial_norm P d -> c=d.
Proof. exact: extended_supremum_unique. Qed.
End Specification.
