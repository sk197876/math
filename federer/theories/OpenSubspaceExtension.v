(** Extension by zero from an open subspace, supporting Federer (1969),
    2.7.16, example (2), printed p. 136: "In case U = V, phi is a left
    |det|^{-n} covariant measure over G", where the linear group G is an
    open subset of X = Hom(V, V) (p. 134). Let S be an open subset of a
    Hausdorff space T, with the relative topology (set_type). For u in K(S)
    the function u' on T which agrees with u on S and vanishes elsewhere
    belongs to K(T) (open_extension_compact): the support of u is a compact
    subset of S, hence closed in T, so u' vanishes near every point outside
    S, and u' agrees with u near every point of S. Consequently a monotone
    Daniell integral mu on K(T) induces the monotone Daniell integral u |->
    mu(u') on K(S) (2.5.2, p. 92; open_restricted_monotone), the integral
    over S of the measure associated with mu. This generalises the extension
    from R^n ~ {0} of PuncturedLebesgueCovariance.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderLimit FunctionLatticeUP MonotoneDaniellIntegralUP
  CompactSupportFunctionUP SubtypeCompactHausdorff IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OpenExtension.
Variable R : realType.
Variable T : topologicalType.
Hypothesis hT : hausdorff_space T.
Variable S : set T.
Hypothesis hS : open S.
Local Notation Y := (set_type S).
Local Notation KY := (@compactly_supported_continuous_functions R Y).
Local Notation KT := (@compactly_supported_continuous_functions R T).

(** Source for [open_extension]: u extended by 0 from the open set S to
    T, for u defined on S, supporting "phi is a left |det|^{-n}
    covariant measure over G" with G open in Hom(V, V), Federer 2.7.16,
    p. 136. Definition. *)
Definition open_extension (u : Y -> R) (x : T) : R :=
  if pselect (S x) is left h then u (exist _ x (mem_set h)) else 0.

(** Source for [open_extensionE]: the extension agrees with u on S,
    supporting Federer 2.7.16, p. 136. *)
Lemma open_extensionE (u : Y -> R) (y : Y) : open_extension u (set_val y) = u y.
Proof.
rewrite /open_extension; case: pselect=> [h|h]; first by congr u; apply: val_inj.
by exfalso; apply: h; exact: set_valP.
Qed.

(** Source for [open_extension_out]: the extension vanishes off S,
    supporting Federer 2.7.16, p. 136. *)
Lemma open_extension_out (u : Y -> R) (x : T) : ~ S x -> open_extension u x = 0.
Proof. by rewrite /open_extension; case: pselect. Qed.

(** Source for [open_extension_compact]: if u in K(S), then its
    extension by 0 belongs to K(T), Federer 2.5.13, p. 106; supporting
    2.7.16, p. 136. Supporting lemma. *)
Lemma open_extension_compact (u : Y -> R) : KY u -> KT (open_extension u).
Proof.
move=> [hu hsu].
pose Su := real_function_support u.
have hSc : compact (set_val @` Su).
  by apply: continuous_compact hsu; apply: continuous_subspaceT=> x; exact: set_type_val_continuous.
have hScl : closed (set_val @` Su) by exact: compact_closed hT hSc.
have hsub : [set x : T | open_extension u x <> 0] `<=` set_val @` Su.
  move=> x hx; have hxS : S x by apply: contrapT=> h; apply: hx; exact: open_extension_out.
  exists (exist _ x (mem_set hxS))=> //; apply: subset_closure=> /=.
  by rewrite -(open_extensionE u (exist _ x (mem_set hxS))).
have hsupp : real_function_support (open_extension u) `<=` set_val @` Su.
  have he : set_val @` Su = closure (set_val @` Su) by exact: (closure_id _).1 hScl.
  by rewrite he; exact: closureS.
split; last by apply: (subclosed_compact (@real_function_support_closed R T _) hSc).
move=> x; case: (pselect (S x))=> [hxS|hxS].
- pose x' : Y := exist _ x (mem_set hxS).
  move=> A hA; rewrite /= nbhs_simpl /=.
  have hA' : nbhs (u x' : real_line_metric R) A by rewrite -(open_extensionE u x'); exact: hA.
  have := hu x' A hA'; rewrite /= nbhs_simpl /= (@nbhsE Y)=> -[W [[O hO hOW] hWx] hWA].
  have hOx : O x by rewrite -hOW in hWx.
  have hN : nbhs x (O `&` S) by apply: open_nbhs_nbhs; split; [exact: openI|split].
  apply: (@filterS _ _ (nbhs_filter _) _ _ _ hN)=> y [hyO hyS] /=.
  pose y' : Y := exist _ y (mem_set hyS).
  rewrite -[y]/(set_val y') open_extensionE; apply: hWA; rewrite -hOW.
  exact: hyO.
- have hN : nbhs x (~` (set_val @` Su)).
    apply: open_nbhs_nbhs; split; first by apply: closed_openC.
    by move=> -[y _ hy]; apply: hxS; rewrite -hy; exact: set_valP.
  move=> A hA; rewrite /= nbhs_simpl /=.
  apply: (@filterS _ _ (nbhs_filter _) _ _ _ hN)=> y hy /=.
  have hy0 : open_extension u y = 0.
    by apply: contrapT=> hne; apply: hy; apply: hsupp; apply: subset_closure.
  by rewrite hy0 -(open_extension_out u hxS); exact: nbhs_singleton hA.
Qed.

(** Source for [open_extension_pointwise]: extension by 0 commutes with
    pointwise operations F with F(0, 0) = 0, supporting the Daniell
    integral on K(S) in Federer 2.7.16, p. 136. Supporting lemma. *)
Lemma open_extension_pointwise (F : R -> R -> R) (f g : Y -> R) : F 0 0 = 0 ->
  open_extension (fun y => F (f y) (g y)) = (fun x => F (open_extension f x) (open_extension g x)).
Proof. by move=> hF; apply: funext=> x; rewrite /open_extension; case: pselect. Qed.

(** Source for [open_restricted_integral]: u |-> mu(u'), the integral
    over the open set S induced by a Daniell integral mu on K(T),
    Federer 2.5.2, p. 92, supporting 2.7.16, p. 136. Definition. *)
Definition open_restricted_integral (mu : (T -> R) -> R) (u : Y -> R) : R := mu (open_extension u).

(** Source for [extended_constant_increases]: a constant sequence
    increases to its value, Federer 2.1.1, p. 51. Supporting lemma. *)
Lemma extended_constant_increases (a : \bar R) : extended_increases_to (fun _ : nat => a) a.
Proof.
split; first by move=> k p _; exact: lexx.
by split=> [c hc|c hc]; exists 0%N.
Qed.

(** Source for [open_restricted_monotone]: u |-> mu(u') is a monotone
    Daniell integral on K(S) whenever mu is one on K(T), Federer 2.5.2,
    p. 92, because extension by 0 preserves the operations, the order
    and increasing convergence; supporting 2.7.16, p. 136. Supporting
    lemma. *)
Lemma open_restricted_monotone (mu : (T -> R) -> R) :
  is_monotone_daniell_integral KT mu -> is_monotone_daniell_integral KY (open_restricted_integral mu).
Proof.
move=> [hadd hscale hmono hinc].
split.
- move=> f g hf hg; rewrite /open_restricted_integral (@open_extension_pointwise (fun a b => a + b) f g (addr0 0)).
  exact: hadd (open_extension_compact hf) (open_extension_compact hg).
- move=> c f hc hf; rewrite /open_restricted_integral.
  rewrite (@open_extension_pointwise (fun a b => c * a) f f (mulr0 c)).
  exact: hscale hc (open_extension_compact hf).
- move=> f g hf hg hfg; apply: hmono; try exact: open_extension_compact.
  by move=> x; rewrite /open_extension; case: pselect=> // h; exact: hfg.
- move=> f g hf hg hfg; apply: hinc; first by move=> k; exact: open_extension_compact.
    exact: open_extension_compact.
  move=> x; rewrite /open_extension; case: pselect=> h; first exact: hfg.
  exact: extended_constant_increases.
Qed.

End OpenExtension.

Arguments open_extension {R T S} u x.
Arguments open_restricted_integral {R T S} mu u.
