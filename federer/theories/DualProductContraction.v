(** Federer (1969), 1.6.5, p. 26, first displayed computation: applying
    upper duality to D_k(xi) wedge D_l(eta) equals contracting xi by
    D_l(eta). This follows from both final laws of 1.5.2. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors ProductContraction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Contraction.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> A_m V K^o 1.
Hypothesis he : is_basis e.
Hypothesis hd : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
Local Notation et := (e_lambda e (val (Lambda_top n))).
Local Notation ot := (omega_lambda h2 omega (Lambda_top n)).

(** Source for [duality_inverse_interior]: Federer 1.6.5, p. 26,
    application of the inverse duality maps in the first display.
    Supporting identity on the whole exterior algebra; no degree
    reindexing changes its underlying vector. *)
Lemma duality_inverse_interior k (hk : (k <= n)%N) (xi : exterior_power V k) :
  left_interior_hom h2 (component_val et) (form_homogeneous (D_p ot hk xi)) =
    component_val xi.
Proof.
have h := congr1 component_val (@D_pK K h2 V n e omega he hd k hk xi).
by rewrite /D_inverse exterior_reindexE D_upperE in h.
Qed.

(** Source for [dual_product_contraction]: Federer 1.6.5, p. 26,
    first equality D^(2n-k-l)(D_k xi wedge D_l eta)=xi contracted
    by D_l eta. Direct formalisation as equality in the exterior
    algebra, so that the equal natural-number degrees need no cast. *)
Theorem dual_product_contraction k l (hk : (k <= n)%N) (hl : (l <= n)%N)
  (hkl : (n <= k+l)%N) (xi : exterior_power V k) (eta : exterior_power V l) :
  component_val (D_upper h2 et (product_contraction_bound hk hl hkl)
    (form_wedge h2 (scalar_bilinear K) (D_p ot hk xi) (D_p ot hl eta))) =
  left_interior_hom h2 (component_val xi) (form_homogeneous (D_p ot hl eta)).
Proof.
rewrite D_upperE form_wedge_hom left_interior_hom_associative.
by rewrite duality_inverse_interior.
Qed.
End Contraction.
