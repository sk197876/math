(** Federer (1969), 2.5.20, p. 114: the graph map h(y)=(g(y),y) is
    continuous and proper, and the support of its image Daniell integral is
    contained in im h. These general compact-source lemmas verify those
    assertions. Source context: CompactFunctionSpaceUP.v *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals topology.
From Federer Require Import ProperMapUP TopologicalProductMaps CompactSupportFunctionUP
  CompactSupportFunctionLattice CompactSupportDaniellSupport DaniellIntegralUP
  DaniellIntegralAlgebra DaniellSpacePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_source_continuous_map_proper]: properness
    of the continuous graph map in Federer 2.5.20, p. 114,
    follows from compactness of Y and the Hausdorff target. *)
Lemma compact_source_continuous_map_proper (Y Z : topologicalType) (u : Y -> Z) :
  compact (@setT Y) -> hausdorff_space Z -> continuous u -> is_proper_map u.
Proof.
move=> hY hh hu K hK.
apply: (@subclosed_compact Y (u @^-1` K) setT _ hY (@subsetT _ _)).
exact: (continuous_closedP u).1 hu _ (compact_closed hh hK).
Qed.

(** Source for [compact_source_pushforward_support]: the support
    of h#gamma is contained in im h in Federer 2.5.20,
    p. 114. Compactness makes the image closed, and a
    test supported outside the image pulls back to zero. *)
Theorem compact_source_pushforward_support (R : realType) (Y Z : topologicalType)
    (u : Y -> Z) (A : (Y -> R) -> R) :
  compact (@setT Y) -> hausdorff_space Z -> continuous u ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  compact_support_daniell_support (daniell_pushforward u A) `<=` u @` setT.
Proof.
move=> hY hh hu hA z hz; apply: contrapT=> hn; apply: hz.
have him : compact (u @` setT) := continuous_compact (continuous_subspaceT hu) hY.
exists (~` (u @` setT)); last exact hn.
split; first by rewrite openC; exact: compact_closed hh him.
move=> f hf hs.
have he : f \o u=(fun _ : Y => (0 : R)).
  apply: funext=> y; change (f (u y)=0).
  apply: (@real_function_zero_off_support R Z f (u y))=> hfy.
  apply: (hs (u y) hfy); by exists y.
rewrite /daniell_pushforward he.
exact: (@daniell_integral_zero R Y (@compactly_supported_continuous_functions R Y) A hA
  (fun _ => 0) (@compactly_supported_zero_function R Y)).
Qed.

(** Source for [daniell_graph_map]: the displayed h(y)=(g(y),y)
    in the second paragraph of Federer 2.5.20, p. 114. *)
Definition daniell_graph_map (X Y : topologicalType) (g : Y -> X) (y : Y) : X*Y := (g y,y).

(** Source for [daniell_graph_map_continuous]: continuity of h
    in Federer 2.5.20, p. 114. *)
Lemma daniell_graph_map_continuous (X Y : topologicalType) (g : Y -> X) :
  continuous g -> continuous (daniell_graph_map g).
Proof.
move=> hg; apply: topological_pair_continuous; first exact hg.
by move=> y; exact: cvg_id.
Qed.

(** Source for [daniell_graph_map_image_fibre]: a point (x,y)
    of im h satisfies g(y)=x, supporting the fibre support
    assertion in Federer 2.5.20, p. 114. *)
Lemma daniell_graph_map_image_fibre (X Y : topologicalType) (g : Y -> X) x y :
  (daniell_graph_map g @` setT) (x,y) -> g y=x.
Proof.
move=> [z _ he]; have hy := congr1 snd he; have hx := congr1 fst he.
by rewrite /daniell_graph_map /= in hy hx; rewrite -hy.
Qed.
