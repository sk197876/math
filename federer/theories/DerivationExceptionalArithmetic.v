(** Finite mass arguments in Federer (1969), 2.9.5, p. 155. A finite mass
    cannot dominate every positive multiple of a positive mass; two distinct
    scalar bounds on the same finite nonnegative mass force that mass to
    vanish. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [finite_all_scaled_bounds_zero]: supporting
    inference phi(A)=0 for bounded A in Q,
    Federer 2.9.5, p. 155. Both masses
    are finite and nonnegative, as supplied by the
    original class M on bounded targets. *)
Lemma finite_all_scaled_bounds_zero (R : realType) (a b : \bar R) :
  0<=a -> a< +oo -> 0<=b -> b< +oo ->
  (forall c : R, (0<c)%R -> c%:E*a<=b) -> a=0.
Proof.
move=> ha haf hb hbf hall.
have hafin : a \is a fin_num by rewrite (ge0_fin_numE ha).
have hbfin : b \is a fin_num by rewrite (ge0_fin_numE hb).
pose r := fine a; pose s := fine b.
have hea : a=r%:E by rewrite /r fineK.
have heb : b=s%:E by rewrite /s fineK.
have hr0 : (0<=r)%R by move: ha; rewrite hea lee_fin.
have hs0 : (0<=s)%R by move: hb; rewrite heb lee_fin.
case: (eqVneq r 0%R)=> [hr|hr]; first by rewrite hea hr.
have hrp : (0<r)%R by rewrite lt_def hr hr0.
pose c := ((s+1)/r)%R.
have hsp : (0<s+1)%R.
  apply: le_lt_trans hs0 _; by rewrite ltrDl ltr01.
have hcp : (0<c)%R by rewrite /c divr_gt0.
have hcr : (c*r=s+1)%R by rewrite /c divfK ?gt_eqF.
have h := hall c hcp; rewrite hea heb -EFinM hcr lee_fin in h.
have hlt : (s<s+1)%R by rewrite ltrDl ltr01.
by have := lt_le_trans hlt h; rewrite ltxx.
Qed.

(** Source for [finite_separated_scaled_bounds_zero]: supporting
    inference phi(A)=0 for bounded A in R(a,b),
    Federer 2.9.5, p. 155. The middle
    value may be infinite; the finite upper bound
    and distinct scalar coefficients are enough. *)
Lemma finite_separated_scaled_bounds_zero (R : realType) (u v : \bar R) (a b : R) :
  0<=u -> u< +oo -> (a<b)%R -> b%:E*u<=v -> v<=a%:E*u -> u=0.
Proof.
move=> hu huf hab hl hh.
have hufin : u \is a fin_num by rewrite (ge0_fin_numE hu).
pose r := fine u.
have he : u=r%:E by rewrite /r fineK.
have hr0 : (0<=r)%R by move: hu; rewrite he lee_fin.
case: (eqVneq r 0%R)=> [hr|hr]; first by rewrite he hr.
have hrp : (0<r)%R by rewrite lt_def hr hr0.
have h := le_trans hl hh; rewrite he -!EFinM lee_fin in h.
have hlt : (a*r<b*r)%R by rewrite ltr_pM2r.
by have := lt_le_trans hlt h; rewrite ltxx.
Qed.
