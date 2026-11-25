(** Federer (1969), 4.1.12, p. 367: turn
    a finite flat unit-ball bound into its exact
    homogeneous bound. This supplements the normed
    source result of 3.1.1 and the function-lattice
    result of 2.5.7 for arbitrary seminormed spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SeminormFunctionalUnitBound.
Variable R:realType.
Variable E:lmodType R.
Variable p:E->R.
Hypothesis hp:is_real_seminorm p.
Variable T:Hom E R^o.
Variable C:R.
Hypothesis hUnit:forall x,p x<=1->`|T x|<=C.

(** Source for [seminorm_functional_unit_nonnegative]: zero
    is in the original flat unit ball, so every
    finite upper bound is nonnegative, supporting
    Federer 4.1.12, p. 367. *)
Lemma seminorm_functional_unit_nonnegative:0<=C.
Proof.
have hZero:p 0<=1 by rewrite (real_seminorm_zero hp) ler01.
have h:=@hUnit 0 hZero.
by rewrite linear0 normr0 in h.
Qed.

(** Source for [seminorm_functional_unit_kernel]: a real
    linear functional bounded on the original seminorm
    unit ball annihilates its zero-seminorm vectors,
    supporting Federer 4.1.12, p. 367. *)
Lemma seminorm_functional_unit_kernel x:p x=0->T x=0.
Proof.
move=>hZero.
apply/eqP;apply/negPn;apply/negP=>hNonzero.
have hPositive:0<`|T x| by rewrite normr_gt0.
pose c:=(C+1)/`|T x|.
have hC:=seminorm_functional_unit_nonnegative.
have hc:0<=c by rewrite /c divr_ge0 // addr_ge0 //;exact:ler01.
have hSmall:p (c*:x)<=1.
  by rewrite (real_seminorm_scale hp) hZero mulr0 ler01.
have h:=@hUnit (c*:x) hSmall.
rewrite linearZ /= normrM (ger0_norm hc) /c mulfVK ?gt_eqF // in h.
by move:h;rewrite gerDl ler10.
Qed.

(** Source for [seminorm_functional_unit_bound]: the exact
    original bound |T(phi)|<=C F_K(phi), including
    zero-seminorm tests, supporting Federer 4.1.12,
    p. 367. The kernel case precedes normalization. *)
Theorem seminorm_functional_unit_bound x:`|T x|<=C * p x.
Proof.
have hNonnegative:=real_seminorm_nonnegative hp x.
case:(eqVneq (p x) 0)=>[hZero|hNonzero].
- rewrite (seminorm_functional_unit_kernel hZero) normr0 hZero mulr0;exact:lexx.
- have hPositive:0<p x by rewrite lt_neqAle eq_sym hNonzero hNonnegative.
  have hSmall:p ((p x)^-1*:x)<=1.
    by rewrite (real_seminorm_scale hp) normfV (ger0_norm (ltW hPositive)) mulVf ?gt_eqF.
  have h:=@hUnit ((p x)^-1*:x) hSmall.
  rewrite linearZ /= normrM normfV (ger0_norm (ltW hPositive)) mulrC in h.
  by rewrite ler_pdivrMr // in h.
Qed.
End SeminormFunctionalUnitBound.
