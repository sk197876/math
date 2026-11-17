(** Federer (1969), 3.4.8(2), p. 326:
    elementary consequences of the exact minimum laws.
    No measure or later stratification theorem is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import AnalyticReductionDepthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_tail_monotone]: removing
    original intersection factors preserves nonemptiness,
    supporting depth in 3.4.8(2), p. 326. *)
Lemma analytic_reduction_tail_monotone n (O:Type) (B:'I_n->set O) d m:
  (d<=m)%N ->has_analytic_reduction_tail B d ->has_analytic_reduction_tail B m.
Proof.
move=>hDM [g hG];exists g=>j hMJ;apply:hG;exact:(leq_trans hDM hMJ).
Qed.

(** Source for [analytic_reduction_depth_tail_criterion]: an
    original directional intersection is nonempty exactly
    at indices at least depth, 3.4.8(2), p. 326. *)
Lemma analytic_reduction_depth_tail_criterion n (O:Type) (B:'I_n->set O) d:
  is_analytic_reduction_depth B d ->forall m,
  has_analytic_reduction_tail B m <->(d<=m)%N.
Proof.
move=>hD m;split;first exact:(analytic_reduction_depth_minimal hD).
move=>hDM;exact:(analytic_reduction_tail_monotone hDM (analytic_reduction_depth_attained hD)).
Qed.

(** Source for [analytic_reduction_depth_empty_family]: if
    every B_j is empty, the original minimum is n,
    including n=0, 3.4.8(2), p. 326. *)
Lemma analytic_reduction_depth_empty_family n (O:Type) (B:'I_n->set O) d:
  (forall j g,~B j g) ->is_analytic_reduction_depth B d ->d = n.
Proof.
move=>hEmpty hD;apply/eqP;rewrite eqn_leq;apply/andP;split.
- exact:(analytic_reduction_depth_bound hD).
- case:(leqP n d)=>// hDN.
  have [g hG]:=analytic_reduction_depth_attained hD.
  have hMember:=hG (Ordinal hDN) (leqnn d).
  exfalso;exact:(hEmpty _ _ hMember).
Qed.

(** Source for [analytic_reduction_depth_monotone]: a larger
    family of directional reduction sets has no larger
    minimum, supporting 3.4.8(2), p. 326. *)
Lemma analytic_reduction_depth_monotone n (O:Type) (B C:'I_n->set O) d e:
  (forall j g,B j g ->C j g) ->
  is_analytic_reduction_depth B d ->is_analytic_reduction_depth C e ->(e<=d)%N.
Proof.
move=>hSubset hD hE;apply:(analytic_reduction_depth_minimal hE).
have [g hG]:=analytic_reduction_depth_attained hD.
exists g=>j hDJ;apply:hSubset;exact:hG.
Qed.
