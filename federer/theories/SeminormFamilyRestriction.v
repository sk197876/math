(** Federer (1969), 4.1.1, p. 344: restricting the seminorms
    to a linear subspace gives precisely the relative topology.
    No closedness of the subspace is needed for this fact. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import Hom RealNormUP RealSeminormOperations OpenFamilyTopologyUP
  InitialOpenTopologyUP DirectedSeminormFamilyUP DirectedSeminormTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SeminormRestriction.
Variable R:realType.
Variables E W:lmodType R.
Variable I:Type.
Variable p:I->E->R.
Variable O:set (set E).
Hypothesis hp:is_directed_seminorm_family p.
Hypothesis hO:is_seminorm_family_topology p O.
Variable inc:Hom W E.

(** Source for [restricted_seminorm_family_directed]: the
    defining seminorms remain directed on a subspace, supporting
    D_K(U,Y) in Federer 4.1.1, p. 344. *)
Lemma restricted_seminorm_family_directed :
  is_directed_seminorm_family (fun i w=>p i (inc w)).
Proof.
constructor.
- exact:directed_seminorm_nonempty hp.
- move=>i; exact:(@real_seminorm_linear_precompose R W E (p i)
    (directed_seminorm_laws hp i) inc (hom_linear inc)).
- move=>i j; have [k hk]:=directed_seminorm_upper_pair hp i j.
  exists k=>w; exact:hk.
Qed.

(** Source for [restricted_seminorm_topology_initial]: the
    seminorms restricted to D_K(U,Y) induce exactly its E-relative
    topology, supporting Federer 4.1.1, p. 344. The argument
    applies to every linear inclusion, including zero spaces. *)
Theorem restricted_seminorm_topology_initial (P:set (set W)) :
  is_seminorm_family_topology (fun i w=>p i (inc w)) P ->
  is_initial_open_topology O inc P.
Proof.
move=>hP; split; first exact:hP.1.
move=>B; split.
- move=>hB.
  pose A:set E:=[set z|exists (w:W) (i:I) (r:R),
    B w /\ 0<r /\ (forall v,p i (inc v-inc w)<r -> B v) /\
      p i (z-inc w)<r].
  have hA:O A.
    apply:(hO.2 A).2=>z [w [i [r [hw [hr [hb hz]]]]]].
    change (is_true (p i (z-inc w)<r)) in hz.
    exists i,(r-p i (z-inc w)); split; first by rewrite subr_gt0.
    move=>y hy; exists w,i,r; split=>//; split=>//; split=>//.
    have ht:=real_seminorm_triangle (directed_seminorm_laws hp i) (y-z) (z-inc w).
    rewrite addrA subrK in ht.
    change (is_true (p i (y-inc w)<r)); lra.
  exists A; split=>//; apply:funext=>v; apply:propext; split.
  + move=>hv; have [i [r [hr hb]]]:=(hP.2 B).1 hB v hv.
    exists v,i,r; split=>//; split=>//; split.
    * move=>w hw; apply:hb; by rewrite linearB.
    * by rewrite subrr (real_seminorm_zero (directed_seminorm_laws hp i)).
  + move=>[w [i [r [hw [hr [hb hv]]]]]]; exact:hb v hv.
- move=>[A [hA ->]]; apply:(hP.2 _).2=>w hw.
  have [i [r [hr hb]]]:=(hO.2 A).1 hA (inc w) hw.
  exists i,r; split=>// v hv; apply:hb; by rewrite -linearB.
Qed.
End SeminormRestriction.
