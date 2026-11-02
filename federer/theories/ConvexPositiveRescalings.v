(** Federer (1969), 3.2.35, p. 271:
    combine two positive radial rescalings using
    the displayed convex-combination identity. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra.
From Federer Require Import InnerConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_positive_rescaling_sum]: the
    displayed identity with c=alpha*a+beta*b in
    Federer 3.2.35, p. 271, specialised to
    the two unit coefficients needed for subadditivity.
    Original convex-set membership gives membership of
    (u+v)/(r+s); no closure or additional interior
    hypothesis replaces the original source set. *)
Lemma convex_positive_rescaling_sum (R:realType) (V:lmodType R)
    (S:set V) (u v:V) (r s:R):
  is_inner_convex S ->0<r ->0<s ->S (r^-1*:u) ->S (s^-1*:v) ->
  S ((r+s)^-1*:(u+v)).
Proof.
move=>hConvex hr hs hu hv.
pose c:R:=r+s.
have hc:0<c by rewrite /c addr_gt0.
have hc0:c!=0 by rewrite gt_eqF.
have hr0:r!=0 by rewrite gt_eqF.
have hs0:s!=0 by rewrite gt_eqF.
have hLambda0:0<=s/c by rewrite divr_ge0 ?ltW.
have hLambda1:s/c<=1.
  rewrite ler_pdivrMr // mul1r /c; lra.
have hOne:1-s/c=r/c.
  by rewrite -{1}(divff hc0) -mulrBl /c addrK.
have hLeft:(r/c)*r^-1=c^-1 by rewrite mulrAC (mulfV hr0) mul1r.
have hRight:(s/c)*s^-1=c^-1 by rewrite mulrAC (mulfV hs0) mul1r.
have hS:=hConvex (r^-1*:u) (s^-1*:v) hu hv (s/c) hLambda0 hLambda1.
by rewrite hOne !scalerA hLeft hRight -scalerDr in hS.
Qed.
