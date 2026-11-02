(** Federer (1969), 1.10.5, p. 48: supporting Hahn-Banach argument for the
    dual norm and positivity. This is the finite-valued case of the interval
    construction printed in 2.4.12, p. 86. Only completeness of the scalar
    field is used in this step, not completeness of the vector space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP PartialLinearMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Interval.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.
Variable G : V -> R^o -> Prop.
Hypothesis hG : linear_graph G.
Hypothesis hdom : forall x c, G x c -> c <= N x.
Variable v : V.

(** Source for [seminorm_adjoin_bounds_ordered]: Federer 1.10.5,
    p. 48, supporting interval inequality from 2.4.12, p. 86:
    f(x)-N(x-v) <= N(y+v)-f(y). It follows from domination on
    x+y and the triangle inequality. *)
Lemma seminorm_adjoin_bounds_ordered x y c d : G x c -> G y d ->
  c-N(x-v) <= N(y+v)-d.
Proof.
move=> hx hy.
have hxy : G (x+y) (c+d) := (proj1 (proj2 hG)) _ _ _ _ hx hy.
have he : (x-v)+(y+v)=x+y by rewrite addrACA addNr addr0.
have ht := real_seminorm_triangle hN (x-v) (y+v).
rewrite he in ht.
have h := le_trans (hdom hxy) ht.
rewrite lerBrDr addrAC lerBlDl.
exact: h.
Qed.

(** Source for [seminorm_adjoin_lower_set]: Federer 1.10.5,
    p. 48, supporting set whose supremum appears in 2.4.12,
    p. 86: all f(x)-N(x-v) for x in the old graph domain. *)
Definition seminorm_adjoin_lower_set : set R :=
  fun r => exists x c, G x c /\ r=c-N(x-v).

(** Source for [seminorm_adjoin_lower_nonempty]: Federer
    1.10.5, p. 48, the interval's lower set is nonempty because
    the old linear graph contains (0,0). *)
Lemma seminorm_adjoin_lower_nonempty : exists r, seminorm_adjoin_lower_set r.
Proof. exists (-N(-v)); exists 0,0; split; first exact: proj1 hG. by rewrite sub0r sub0r. Qed.

(** Source for [seminorm_adjoin_lower_upper]: Federer 1.10.5,
    p. 48, every proposed upper endpoint bounds the whole lower set. *)
Lemma seminorm_adjoin_lower_upper y d : G y d ->
  ubound seminorm_adjoin_lower_set (N(y+v)-d).
Proof.
move=> hy r [x [c [hx ->]]]; exact: seminorm_adjoin_bounds_ordered hx hy.
Qed.

(** Source for [seminorm_adjoin_lower_bounded]: Federer
    1.10.5, p. 48, supporting real boundedness of the interval:
    setting y=0 bounds every lower endpoint by N(v). *)
Lemma seminorm_adjoin_lower_bounded : exists r, ubound seminorm_adjoin_lower_set r.
Proof.
exists (N v).
have h := seminorm_adjoin_lower_upper (proj1 hG).
by rewrite add0r subr0 in h.
Qed.

(** Source for [seminorm_adjoin_value]: Federer 1.10.5,
    p. 48, choose the supremum of the lower interval endpoints
    as the value on the new vector, following 2.4.12, p. 86. *)
Definition seminorm_adjoin_value := sup seminorm_adjoin_lower_set.

(** Source for [seminorm_adjoin_value_lower]: Federer 1.10.5,
    p. 48, the chosen value is above every lower endpoint. *)
Lemma seminorm_adjoin_value_lower x c : G x c -> c-N(x-v) <= seminorm_adjoin_value.
Proof.
move=> hx; rewrite /seminorm_adjoin_value.
apply: ub_le_sup; first exact: seminorm_adjoin_lower_bounded.
exists x,c; by split.
Qed.

(** Source for [seminorm_adjoin_value_upper]: Federer 1.10.5,
    p. 48, the same value is below every upper endpoint, proving
    that the scalar needed in the single-vector extension exists. *)
Lemma seminorm_adjoin_value_upper x c : G x c -> seminorm_adjoin_value <= N(x+v)-c.
Proof.
move=> hx; rewrite /seminorm_adjoin_value.
apply: ge_sup; first exact: seminorm_adjoin_lower_nonempty.
exact: seminorm_adjoin_lower_upper hx.
Qed.
End Interval.
