(** Federer (1969), 3.4.8(2), p. 326:
    finite index minimisation supplies the original depth.
    At n the intersection is the whole nonempty group. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import AnalyticReductionDepthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_depth_exists]: the infimum
    defining depth is attained, 3.4.8(2), p. 326.
    Nonemptiness of O(n) is the only group fact used. *)
Theorem analytic_reduction_depth_exists n (O:Type) (g0:O) (B:'I_n->set O):
  exists d,is_analytic_reduction_depth B d.
Proof.
pose P m:=`[<has_analytic_reduction_tail B m>].
have hN:has_analytic_reduction_tail B n.
  exists g0=>j hj.
  have hFalse:=leq_ltn_trans hj (ltn_ord j).
  by rewrite ltnn in hFalse.
have hExists:exists m,P m by exists n;apply/asboolP.
have [d /asboolP hD hMinimal]:=@ex_minnP P hExists.
exists d;constructor.
- apply:hMinimal;exact/asboolP.
- exact:hD.
- move=>m hM;apply:hMinimal;exact/asboolP.
Qed.

(** Source for [analytic_reduction_depth_unique]: the least
    index is unique, 3.4.8(2), p. 326. *)
Lemma analytic_reduction_depth_unique n (O:Type) (B:'I_n->set O) d e:
  is_analytic_reduction_depth B d ->is_analytic_reduction_depth B e ->d = e.
Proof.
move=>hD hE;apply/eqP;rewrite eqn_leq;apply/andP;split.
- exact:(analytic_reduction_depth_minimal hD (analytic_reduction_depth_attained hE)).
- exact:(analytic_reduction_depth_minimal hE (analytic_reduction_depth_attained hD)).
Qed.
