(** Federer (1969), 2.9.1, p. 153: the V derivate D(psi,phi,V,x) is the
    covering-relation limit of psi(S)/phi(S). The function and its quotient
    are partial under the original arithmetic convention 2.1.1, p. 51: zero
    denominators and infinity/infinity are undefined. No such regularity is
    built into this definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealConventions PartialFunctionUP
  CoveringRelationUP CoveringRelationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_ratio_function]: quotient function
    psi/phi in Federer 2.9.1, p. 153. Its graph
    uses the original partial arithmetic of 2.1.1, p. 51,
    with no artificial value assigned to a zero denominator. *)
Definition measure_ratio_function (R : realType) (X : Type)
    (psi phi : set X -> \bar R) : partial_function (set X) (\bar R).
Proof.
refine (@Build_partial_function (set X) (\bar R)
  (fun S y => extended_divide (psi S) (phi S)=Some y) _).
move=> S y z hy hz; rewrite hy in hz; by case: hz.
Defined.

(** Source for [measure_ratio_graph]: graph equation for
    the quotient in Federer 2.9.1, p. 153.
    This exposes the arithmetic domain without evaluating an
    undefined ratio. *)
Lemma measure_ratio_graph (R : realType) (X : Type)
    (psi phi : set X -> \bar R) S y :
  partial_function_graph (measure_ratio_function psi phi) S y <->
    extended_divide (psi S) (phi S)=Some y.
Proof. by []. Qed.

(** Source for [measure_ratio_zero_denominator]: supporting
    undefined-ratio boundary for Federer 2.9.1, p. 153,
    under 2.1.1, p. 51. The null-denominator fiber
    is treated separately in the existence proof 2.9.5,
    p. 154; it is not filled by a default value. *)
Lemma measure_ratio_zero_denominator (R : realType) (X : Type)
    (psi phi : set X -> \bar R) S :
  phi S=0 -> ~ partial_function_domain (measure_ratio_function psi phi) S.
Proof.
move=> hphi [y hy]; move: hy; rewrite /measure_ratio_function /= hphi extended_divide_zero.
by discriminate.
Qed.

(** Source for [measure_ratio_positive_finite_denominator]:
    supporting evaluation on positive finite denominator cells
    for Federer 2.9.1, p. 153. The numerator
    may be infinite; bounded cells in the original class M
    make both measures finite, a stronger special case. *)
Lemma measure_ratio_positive_finite_denominator (R : realType) (X : Type)
    (psi phi : set X -> \bar R) S :
  0<phi S -> phi S \is a fin_num ->
  partial_function_graph (measure_ratio_function psi phi) S (psi S/phi S).
Proof.
move=> hp hf; rewrite /measure_ratio_function /= /extended_divide (gt_eqF hp) hf orbT.
by [].
Qed.

(** Source for [measure_derivate]: direct definition of D(psi,phi,V,.) in
    Federer 2.9.1, p. 153 The graph requires the fine-point upper and lower
    covering limits to agree. Existence almost everywhere is a later
    theorem, not a premise of this definition. *)
Definition measure_derivate (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop) :=
  covering_relation_limit V (measure_ratio_function psi phi).

(** Source for [measure_derivate_graph]: the defining
    limit equation for Federer 2.9.1, p. 153,
    expanded using 2.8.16, p. 151. It keeps
    the original partial domain explicit. *)
Lemma measure_derivate_graph (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop) x y :
  partial_function_graph (measure_derivate psi phi V) x y <->
    covering_relation_fine_at V x /\
    covering_upper_limit V (measure_ratio_function psi phi) x=y /\
    covering_lower_limit V (measure_ratio_function psi phi) x=y.
Proof. by []. Qed.
