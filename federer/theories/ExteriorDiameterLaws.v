(** Supporting supremum laws for Federer (1969), 2.10.3, pp. 171–172. Relate
    the abstract specification to the printed endpoint formula and derive
    monotonicity without unfolding a witness. Source context and scope:
    ExteriorDiameterUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  FiniteExteriorPowers ExteriorNorm ExteriorProductFactors ExtendedSupremumUP ExteriorDiameterUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [exterior_difference_equal_endpoints]:
    supporting zero value in the supremum of Federer
    2.10.3, p. 171. In positive degree, taking the
    same endpoints for every factor gives the zero
    exterior vector, hence zero norm. *)
Lemma exterior_difference_equal_endpoints (R : realType) (n m : nat)
    (a : 'I_m -> R_n R n) : (0<m)%N -> exterior_difference_norm a a=0.
Proof.
move=> hm; rewrite /exterior_difference_norm /exterior_difference_product.
have hz : @e_lambda R (Choice.clone 'I_m _) (R_n R n)
    (fun i => a i-a i) m (ord_tuple m)=0.
  apply: (@exterior_product_zero_entry R (Choice.clone 'I_m _) (R_n R n)
    (fun i => a i-a i) m (ord_tuple m) (@Ordinal m 0 hm)).
  - by rewrite /ord_tuple /= mem_enum.
  - exact: subrr.
by rewrite hz exterior_norm_zero.
Qed.

(** Source for [exterior_diameter_raw_values]: supporting
    exact nonempty positive-degree agreement with the
    printed supremum in Federer 2.10.3, p. 171.
    The auxiliary adjoined zero is already one of the
    printed endpoint values, so no gauge value is altered. *)
Lemma exterior_diameter_raw_values (R : realType) (n m : nat) (A : set (R_n R n)) :
  (0<m)%N -> A !=set0 -> exterior_diameter_values m A=
    [set d | exists a b : 'I_m -> R_n R n,
      (forall i, A (a i)) /\ (forall i, A (b i)) /\ d=exterior_difference_norm a b].
Proof.
move=> hm [x hx]; apply/seteqP; split=> d hd; last by right.
case: hd=> [->|hd]=> //.
exists (fun _ => x),(fun _ => x); split=> //; split=> //.
exact: esym (exterior_difference_equal_endpoints (fun _ : 'I_m => x) hm).
Qed.

(** Source for [exterior_diameter_endpoint_upper]: supporting
    upper-bound clause for each exterior-product norm in
    Federer 2.10.3, p. 171. No attainment or boundedness
    of the full supremum is asserted. *)
Lemma exterior_diameter_endpoint_upper (R : realType) (n m : nat)
    (A : set (R_n R n)) (d : \bar R) (a b : 'I_m -> R_n R n) :
  is_exterior_diameter m A d -> (forall i, A (a i)) -> (forall i, A (b i)) ->
  ((exterior_difference_norm a b)%:E<=d)%E.
Proof.
move=> hd ha hb; apply: (extended_supremum_upper hd); right.
exists a,b; by split=> //; split.
Qed.

(** Source for [exterior_diameter_least_bound]: supporting
    least-bound clause for the supremum in Federer
    2.10.3, p. 171. Include the auxiliary zero bound
    explicitly; for positive-degree nonempty sets it follows
    already from equal endpoints. *)
Lemma exterior_diameter_least_bound (R : realType) (n m : nat)
    (A : set (R_n R n)) (d e : \bar R) : is_exterior_diameter m A d ->
  (0<=e)%E -> (forall a b : 'I_m -> R_n R n,
    (forall i, A (a i)) -> (forall i, A (b i)) -> ((exterior_difference_norm a b)%:E<=e)%E) ->
  (d<=e)%E.
Proof.
move=> hd he hb; apply: (extended_supremum_least hd)=> x [->|[a [b [ha [hc ->]]]]]=> //.
exact: hb a b ha hc.
Qed.

(** Source for [exterior_diameter_inclusion_bound]: supporting
    monotonicity of the exterior-diameter gauge of Federer
    2.10.3, p. 171. Supremum specifications are used
    directly, independently of the existence construction. *)
Lemma exterior_diameter_inclusion_bound (R : realType) (n m : nat)
    (A B : set (R_n R n)) (d e : \bar R) :
  is_exterior_diameter m A d -> is_exterior_diameter m B e -> A `<=` B -> (d<=e)%E.
Proof.
move=> hd he hAB; apply: (exterior_diameter_least_bound hd (exterior_diameter_nonnegative he)).
move=> a b ha hb; exact: exterior_diameter_endpoint_upper he
  (fun i => hAB _ (ha i)) (fun i => hAB _ (hb i)).
Qed.
