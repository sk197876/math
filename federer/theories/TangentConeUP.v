(** Federer (1969), 3.1.21, pp. 233–234: intrinsic tangent cones
    in an arbitrary normed real vector space. These are predicates
    on the supplied norm and set, without a selected construction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_tangent_cone]: the opening definition of
    Tan(S,a) in Federer 3.1.21, p. 233. Paraphrase: every positive
    epsilon admits x in S and r>0 with both |x-a| and |r(x-a)-v|
    less than epsilon. Neither a in S nor finite dimension is imposed. *)
Definition norm_tangent_cone (R:realType) (X:lmodType R)
    (N:X->R) (S:set X) (a:X) : set X := fun v=>
  forall e:R,0<e -> exists (x:X) (r:R),
    S x /\ 0<r /\ N (x-a)<e /\ N (r*:(x-a)-v)<e.

(** Source for [norm_tangent_bundle]: Tan(S)=(S times X)
    intersect {(a,v):v in Tan(S,a)}, Federer 3.1.21, p. 233.
    This definition applies to arbitrary subsets, before any
    submanifold or bundle regularity theorem is proved. *)
Definition norm_tangent_bundle (R:realType) (X:lmodType R)
    (N:X->R) (S:set X) : set (X*X) :=
  fun av=>S av.1 /\ norm_tangent_cone N S av.1 av.2.
