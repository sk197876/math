(** Federer (1969), 4.1.1, p. 344: a separating seminorm
    family generates a Hausdorff topology. This supporting proof
    uses two disjoint balls of half their seminorm distance. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import RealNormUP OpenFamilyTopologyUP OpenVectorTopologyUP
  DirectedSeminormFamilyUP DirectedSeminormTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [seminorm_family_hausdorff]: the Hausdorff
    assertion for E(U,Y), Federer 4.1.1, p. 344, follows from
    separation by its order-zero singleton seminorms. *)
Theorem seminorm_family_hausdorff (R:realType) (E:lmodType R)
    (I:Type) (p:I->E->R) (O:set (set E)) :
  is_directed_seminorm_family p -> is_seminorm_family_topology p O ->
  seminorm_family_separates p -> open_family_hausdorff O.
Proof.
move=>hp hO hSep x y hxy.
have hSome:exists i,p i (x-y)<>0.
  case:(pselect (exists i,p i (x-y)<>0))=>// hNone.
  have hz:x-y=0.
    apply:hSep=>i; case:(pselect (p i (x-y)=0))=>// hi.
    exact:False_ind _ (hNone (ex_intro _ i hi)).
  have he:x=y by apply/eqP; rewrite -subr_eq0 hz eqxx.
  exact:False_ind _ (hxy he).
have [i hi]:=hSome.
have hd:0<p i (x-y).
  rewrite lt_def (real_seminorm_nonnegative (directed_seminorm_laws hp i)) andbT.
  apply/eqP; exact:hi.
pose r:=p i (x-y)/2.
have hr:0<r by rewrite /r divr_gt0 // ltr0n.
exists [set z|p i (z-x)<r],[set z|p i (z-y)<r].
split; first exact:(@seminorm_family_ball_open R E I p O hp hO i x r).
split; first exact:(@seminorm_family_ball_open R E I p O hp hO i y r).
split; first by rewrite /= subrr (real_seminorm_zero (directed_seminorm_laws hp i)).
split; first by rewrite /= subrr (real_seminorm_zero (directed_seminorm_laws hp i)).
move=>z [hzx hzy].
change (is_true (p i (z-x)<r)) in hzx.
change (is_true (p i (z-y)<r)) in hzy.
have ht:=real_seminorm_triangle (directed_seminorm_laws hp i) (x-z) (z-y).
rewrite addrA subrK (real_seminorm_subtract (directed_seminorm_laws hp i) x z) in ht.
have hlt:=ltrD hzx hzy.
rewrite /r -splitr in hlt.
have hBad:p i (x-y)<p i (x-y):=le_lt_trans ht hlt.
by rewrite ltxx in hBad.
Qed.
