(** Federer (1969), 3.1.22, p. 235: the tangent
    cone of a singleton supports the zero-on-a-subset differential law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import RealNormUP TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_tangent_singleton]: supporting the opening
    zero-on-S observation of Federer 3.1.22, p. 235:
    a singleton has precisely the zero tangent at its point.
    The normed space may have dimension zero. *)
Lemma norm_tangent_singleton (R:realType) (X:lmodType R) (N:X->R)
    (hN:is_real_norm N) c : norm_tangent_cone N [set c] c=[set 0].
Proof.
apply/seteqP; split=>v.
- move=>hv.
  have hnv:=real_seminorm_nonnegative hN.1 v.
  have hz:N v=0.
    case:(eqVneq (N v) 0)=>// hn.
    have hp:0<N v by rewrite lt_def hn hnv.
    have [x [r [hx [hr [hxc hxv]]]]]:=hv _ hp.
    rewrite hx subrr scaler0 sub0r (real_seminorm_negate hN.1) in hxv.
    by rewrite ltxx in hxv.
  exact: hN.2 hz.
- move=>-> e he; exists c,1; split=>//; split; first exact: ltr01.
  by rewrite subrr scaler0 subr0 (real_seminorm_zero hN.1); split.
Qed.
