(** Federer (1969), 3.2.13, p. 251: the finite
    Gamma product telescopes at exponent one. This elementary
    algebraic lemma records every nonzero denominator explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_shifted_telescoping_product]: the
    cancellation of consecutive Gamma half-integer factors in the
    last displayed formula of Federer 3.2.13, p. 251. *)
Lemma positive_shifted_telescoping_product (R:realType) (g:nat->R) (m k:nat):
  (forall j,0<g j) ->
  (\prod_(j<k) (g ((m+j)%N)*g j.+1/(g j*g ((m+j)%N).+1)))=
    g m*g k/(g ((m+k)%N)*g 0%N).
Proof.
move=>hg.
have hNe j:g j!=0:=lt0r_neq0 (hg j).
elim:k=>[|k ih].
- rewrite big_ord0 addn0 divff // mulf_eq0 (negbTE (hNe m)) (negbTE (hNe 0%N)).
  by [].
- rewrite big_ord_recr /= ih addnS.
  field; by rewrite ?mulf_eq0 ?(negbTE (hNe (m+k)%N)) ?(negbTE (hNe 0%N))
    ?(negbTE (hNe k)) ?(negbTE (hNe ((m+k)%N).+1)).
Qed.
