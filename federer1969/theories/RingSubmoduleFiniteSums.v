(** Federer (1969), 3.4.7, p. 325: finite
    sums of transverse polynomial terms remain in the
    original remainder module. This supporting lemma uses
    only the proved abstract submodule laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingSubmoduleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [ring_submodule_sequence_sum]: a submodule
    contains a finite sum of its elements, supporting
    the remainder argument in 3.4.7, p. 325. *)
Lemma ring_submodule_sequence_sum (A:nzRingType) (V:lmodType A)
    (M:V->Prop) (hM:is_ring_submodule M) (F:seq V):
  (forall x,x \in F ->M x) ->M (\sum_(x<-F) x).
Proof.
elim:F=>[|x F ih] hF.
- rewrite big_nil;exact:ring_submodule_zero hM.
- rewrite big_cons;apply:(@ring_submodule_add A V M hM).
  + exact:hF x (mem_head x F).
  + apply:ih=>y hy;apply:hF;by rewrite in_cons hy orbT.
Qed.

(** Source for [ring_submodule_mapped_sum]: a finite
    sum of the original polynomial term family remains
    in its module, supporting 3.4.7, p. 325. *)
Lemma ring_submodule_mapped_sum (A:nzRingType) (V:lmodType A)
    (M:V->Prop) (hM:is_ring_submodule M) (I:eqType) (F:seq I) (f:I->V):
  (forall i,i \in F ->M (f i)) ->M (\sum_(i<-F) f i).
Proof.
elim:F=>[|i F ih] hF.
- rewrite big_nil;exact:ring_submodule_zero hM.
- rewrite big_cons;apply:(@ring_submodule_add A V M hM).
  + exact:hF i (mem_head i F).
  + apply:ih=>j hj;apply:hF;by rewrite in_cons hj orbT.
Qed.
