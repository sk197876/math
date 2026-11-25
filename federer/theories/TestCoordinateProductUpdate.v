(** Federer (1969), 4.1.3, p. 348: replacing one factor
    in the coordinate product isolates a linear factor. This
    verifies the multilinearity needed by the tensor universal
    property of 1.1.1, p. 9. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import FamilyUpdate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [test_coordinate_product_update]: isolate one
    actual factor of the product in Federer 4.1.3, p. 348. *)
Lemma test_coordinate_product_update (R:realType) n (V:Type)
    (a:V->R->R) (f:{dffun forall i:'I_n,V}) (v:V) (i:'I_n)
    (x:'I_n->R):
  \prod_j a (@family_with n (fun _=>V) f i v j) (x j)=
    a v (x i)*\prod_(j | j!=i) a (f j) (x j).
Proof.
rewrite (bigD1 i) //= family_with_in.
congr (_*_); apply:eq_bigr=>j hj.
by rewrite family_with_out // eq_sym.
Qed.
