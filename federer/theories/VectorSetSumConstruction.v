(** Private existence proof for Federer (1969), 3.2.41, printed
    p. 277: the original pair sums satisfy the independent least-set
    laws. Only VectorSetSumSealed.v and the assumptions audit may import
    this construction. Downstream proofs use VectorSetSumUP.v and the
    public opaque sum laws; no construction is exposed as an extra premise. *)
From mathcomp Require Import all_boot all_algebra classical_sets.
From Federer Require Import VectorSetSumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [vector_set_sum_exists]: existence of the independently
    specified set A+B in Federer 3.2.41, p. 277. The pair-image set
    is a witness for the laws, including empty factors. *)
Theorem vector_set_sum_exists (V : zmodType) (A B : set V) :
  exists C, is_vector_set_sum A B C.
Proof.
exists [set z | exists a b, A a /\ B b /\ z=a+b]; constructor.
- move=> a b ha hb; exists a,b; by split=> //; split.
- move=> D hD z [a [b [ha [hb ->]]]]; exact: hD a b ha hb.
Qed.
