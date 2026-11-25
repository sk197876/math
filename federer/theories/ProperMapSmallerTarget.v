(** Federer (1969), 4.1.9, p. 363: a fixed-time
    inclusion takes the original support into its
    closed cylinder. This supporting target restriction
    reuses compact subspace images from 2.2.17,
    p. 72, as used for proper maps in 4.1.7, p. 359. *)
From mathcomp Require Import all_boot boolp functions classical_sets topology.
From Federer Require Import ProperMapUP IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section ProperMapSmallerTarget.
Variables X Y:topologicalType.
Variables A B:set Y.
Hypothesis hAB:A `<=` B.
Variable g:X->set_type B.
Hypothesis hImage:forall x,A (set_val (g x)).

(** Source for [proper_map_smaller_target_map]: the same
    original map with values in its specified smaller
    target, supporting the exact cylinder restriction
    in Federer 4.1.9, p. 363. No point values change. *)
Definition proper_map_smaller_target_map:X->set_type A:=
  fun x=>exist _ (set_val (g x)) (mem_set (hImage x)).

(** Source for [proper_map_smaller_target]: a map proper
    into B remains proper into a subset A containing
    its image, supporting the fixed-time properness
    in Federer 4.1.9, p. 363. A need not be
    closed in B; the original subspace topology is retained. *)
Theorem proper_map_smaller_target:
  is_proper_map g->is_proper_map proper_map_smaller_target_map.
Proof.
move=>hProper K hK.
pose C:set Y:=set_val @` K.
have hC:@compact Y C.
  apply:continuous_compact hK;exact:continuous_subspaceT (@set_type_val_continuous Y A).
have hCB:C `<=` B.
  move=>y [z _ <-];apply:hAB;exact:set_valP z.
have hCompact:@compact (set_type B) (set_val @^-1` C).
  exact:(@set_type_compact_preimage Y B C hC hCB).
have hPre:=hProper (set_val @^-1` C) hCompact.
have hEqual:proper_map_smaller_target_map @^-1` K=g @^-1` (set_val @^-1` C).
  apply:funext=>x;apply:propext;split.
  - move=>hx;exists (proper_map_smaller_target_map x);by [].
  - move=>[z hz hzx].
    have hSame:z=proper_map_smaller_target_map x.
      apply:val_inj;exact:hzx.
    exact:(eq_ind z K hz (proper_map_smaller_target_map x) hSame).
by rewrite hEqual.
Qed.
End ProperMapSmallerTarget.
