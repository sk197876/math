(** Federer (1969), 4.1.8, p. 362: the
    original finite-product laws determine the actual
    rectangular current uniquely. The proof is finite
    induction through the existing binary products. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces OrientedRectangleCurrentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [oriented_rectangle_current_unique]: the
    original ordered finite product is determined
    uniquely by its original factors, supporting
    Federer 4.1.8, p. 362. *)
Theorem oriented_rectangle_current_unique (R:realType) (h2:(1+1:R)!=0)
    (P Q:forall f:seq (oriented_segment_factor R),@oriented_rectangle_space R h2 f (size f)):
  @is_oriented_rectangle_current R h2 P ->@is_oriented_rectangle_current R h2 Q ->P = Q.
Proof.
move=>[hPE [hPS hPC]] [hQE [hQS hQC]].
apply:functional_extensionality_dep=>f.
elim:f=>[|a t hTail];first by rewrite hPE hQE.
case:t hTail=>[|b t] hTail;first by rewrite hPS hQS.
by rewrite hPC hQC hTail.
Qed.
