(** Private existence witness for the finite
    suprema G_i=sup im ||D^i mu||
    in Federer (1969), 3.1.13, p. 225.
    The existing least-bound norm specification is reused. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import UniformFunctionNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_function_norm_exists]:
    a finite global bound proves existence
    of the scalar supremum used for G_i,
    Federer 3.1.13, p. 225.
    Adding zero fixes the empty-domain convention;
    it has no effect for nonnegative
    functions on the nonempty vector-space domain. *)
Theorem bounded_function_norm_exists (R : realType) (X : Type) (f : X->R) :
  (exists C : R, 0<=C /\ forall x, `|f x|<=C) ->
  exists n, is_uniform_function_norm f n.
Proof.
move=>[C [hC hbound]].
pose S := [set t : R | t=0 \/ exists x, t=`|f x|].
have hs0 : S 0 by left.
have hs : S !=set0 by exists 0.
have hb : has_ubound S.
  exists C=>t [->|[x ->]]; [exact hC|exact: hbound].
exists (sup S); constructor.
- exact: (ub_le_sup hb hs0).
- move=>x; apply: (ub_le_sup hb); right; by exists x.
- move=>d hd hdF; apply: (ge_sup hs)=>t [->|[x ->]]; [exact hd|exact: hdF].
Qed.
