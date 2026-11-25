(** Federer (1969), 1.6.5, p. 26, evaluation of D_l on the trailing basis
    product. The computation is an endpoint-inclusive consequence of the
    inverse duality law in 1.5.2, pp. 22-23. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors InitialComplementSequence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section FinalBlock.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable N : nat.
Variable e : 'I_N -> V.
Variable omega : 'I_N -> A_m V K^o 1.
Hypothesis he : is_basis e.
Hypothesis hd : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
Variable n : nat.
Hypothesis hn : (n <= N)%N.
Local Notation lambda := (Lambda_initial hn).
Local Notation et := (e_lambda e (val (Lambda_top N))).
Local Notation ot := (omega_lambda h2 omega (Lambda_top N)).

(** Source for [right_final_block]: Federer 1.6.5, p. 26,
    D_l(eta) equals the product of the first n-l dual basis forms
    when eta is the product of the last l basis vectors. Direct
    formula on the whole exterior algebra, without degree casts. *)
Theorem right_final_block :
  right_interior_hom (component_val (e_lambda e (val (top_complement lambda))))
    (form_homogeneous ot) = form_homogeneous (omega_lambda h2 omega lambda).
Proof.
have h := @D_upperK K h2 V N e omega he hd n hn (omega_lambda h2 omega lambda).
rewrite (@D_upper_basis K h2 V N e omega he hd n hn lambda)
  /top_complement initial_complement_N expr0 scale1r in h.
apply: hom_ext => z.
have hz := congr1 (fun alpha => form_homogeneous alpha z) h.
rewrite /D_upper_inverse form_reindexE D_pE in hz.
exact: hz.
Qed.
End FinalBlock.

(** Source for [omega_lambda_initial_product]: Federer 1.6.5,
    p. 26, product of the first n-l dual basis forms. Supporting
    identity between the increasing-index notation and the ordered
    product of the restricted family. *)
Lemma omega_lambda_initial_product (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) N (omega : 'I_N -> A_m V K^o 1) n (hn : (n <= N)%N) :
  omega_lambda h2 omega (Lambda_initial hn) =
    one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) (fun i => omega (widen_ord hn i)).
Proof.
rewrite /omega_lambda.
congr (one_forms_wedge _ _ _ _).
apply: funext => i.
by rewrite /Lambda_initial /initial_tuple tnth_mktuple.
Qed.
