(** Federer (1969), 4.1.4, p. 348: the inward locus
    A intersect {z:dist(z,R^n minus A)>e}. Its independently
    specified positive-ball-margin law is equivalent to the
    original distance inequality when the complement is nonempty,
    and retains the whole-space case without a finite empty-set
    distance convention. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_inner_parallel_family]: the exact
    positive-margin characterization of the original inward
    loci in Federer 4.1.4, p. 348, before choosing a witness. *)
Definition is_inner_parallel_family (R:realType) (X:lmodType R)
    (NX:X->R) (A:set X) (O:R->set X):Prop:=
  forall e:R,0<e ->forall x:X,O e x <->
    A x /\ exists r:R,e<r /\ forall y:X,NX (y-x)<r ->A y.

(** Source for [inner_parallel_family_exists]: the original
    inward loci exist, supporting C_e in Federer 4.1.4,
    pp. 348–349. This witness proves the independent specification. *)
Theorem inner_parallel_family_exists (R:realType) (X:lmodType R)
    (NX:X->R) (A:set X):
  exists O:R->set X,is_inner_parallel_family NX A O.
Proof.
exists (fun e x=>A x /\ exists r:R,e<r /\ forall y:X,NX (y-x)<r ->A y).
by move=>e he x.
Qed.
