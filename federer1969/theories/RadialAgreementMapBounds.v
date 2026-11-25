(** Federer (1969), 4.1.15, p. 372: the original
    displacement and exact agreement estimates for G_r.
    The maps need not have any regularity for these
    pointwise assertions. *)
From mathcomp Require Import all_boot all_order all_algebra
  reals classical_sets.
From Federer Require Import RealNormUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct RadialShrinkMapSealed
  RadialShrinkMapDisplacement RadialShrinkMapNorm RadialAgreementMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section RadialAgreementMapBounds.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Variable r:R.
Hypothesis hr:0<r.
Variables f g G:X->Y.
Hypothesis hG:is_radial_agreement_map r hr f g G.
Local Notation P:=(@RadialShrinkMap.value R nu r hr).
Local Notation hP:=(@RadialShrinkMap.laws R nu r hr).

(** Source for [radial_agreement_displacement]: the literal
    |G_r(x)-g(x)|<=r assertion in 4.1.15, p. 372. *)
Theorem radial_agreement_displacement x:NY (G x-g x)<=r.
Proof.
rewrite (hG x).
have hDifference:f x+P (g x-f x)-g x= P (g x-f x)-(g x-f x).
  rewrite opprB addrA.
  congr (_-g x);exact:addrC.
rewrite hDifference;exact:(@radial_shrink_displacement_bound R nu r hr P hP (g x-f x)).
Qed.

(** Source for [radial_agreement_closed_locus]: the literal
    G_r(x)=f(x) when |g(x)-f(x)|<=r assertion in
    Federer 4.1.15, p. 372. *)
Theorem radial_agreement_closed_locus x:
  NY (g x-f x)<=r ->G x=f x.
Proof.
move=>hx;rewrite (hG x) (@radial_shrink_closed_inner R nu r hr P hP (g x-f x) hx).
by rewrite addr0.
Qed.

(** Source for [radial_agreement_exact_locus]: the radial
    definition in 4.1.15, p. 372, also gives the
    converse, so no larger agreement region is assumed. *)
Theorem radial_agreement_exact_locus x:
  G x=f x <-> NY (g x-f x)<=r.
Proof.
split;last exact:radial_agreement_closed_locus.
move=>hx;apply:(@radial_shrink_zero_iff R nu r hr P hP (g x-f x)).1.
have hZero:=congr1 (fun y:Y=>y-f x) hx.
by rewrite (hG x) addrAC !subrr add0r in hZero.
Qed.

(** Source for [radial_agreement_common_zero]: the defining
    G_r formula of 4.1.15, p. 372, vanishes wherever
    both inputs vanish. This preserves the common compact
    carrier of the original local smoothing argument. *)
Theorem radial_agreement_common_zero x:
  f x=0 ->g x=0 ->G x=0.
Proof.
move=>hf hg;rewrite (hG x) hf hg subrr (@radial_shrink_zero R nu r hr P hP).
by rewrite addr0.
Qed.

(** Source for [radial_agreement_common_carrier]: if f and
    g vanish off K, their original G_r does too,
    supporting the smoothing paragraph of 4.1.15, p. 372.
    No compactness or nonemptiness of K is needed here. *)
Theorem radial_agreement_common_carrier (K:classical_sets.set X):
  (forall x,~K x->f x=0) ->(forall x,~K x->g x=0) ->
  forall x,~K x->G x=0.
Proof.
move=>hf hg x hx;exact:radial_agreement_common_zero (hf x hx) (hg x hx).
Qed.
End RadialAgreementMapBounds.
