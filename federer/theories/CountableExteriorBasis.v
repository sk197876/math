(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import ExteriorCore.
From Federer Require Import LinearBasis FiniteCoordinates ExteriorIndices
  FiniteExteriorPowers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.2, the basis e_1,e_2,e_3,...: every vector, exterior
    product, and finite linear combination lies in some finite initial
    span. The projections used here come from the given basis itself. *)
Section InitialSpans.
Variable K : fieldType.
Variable V : lmodType K.
Variable e : nat -> V.
Hypothesis he : is_basis e.

(** Source for [prefix_inclusion]: Federer (1969), 1.3.2, pp. 14-15, basis
    e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Definition or construction used to
    formalise this passage. *)
Definition prefix_inclusion n : {linear coordinate_space K n -> V} :=
  linear_comp (basis_synthesis (fun i : 'I_n => e (val i)))
    (GRing.Linear.clone _ _ _ _ (@coordinate_to_free K n) _).
Arguments prefix_inclusion {n}.
(** Source for [prefix_retraction]: Federer (1969), 1.3.2, pp. 14-15, basis
    e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Definition or construction used to
    formalise this passage. *)
Definition prefix_retraction n (v : V) : coordinate_space K n :=
  [ffun i => basis_coordinates he v (val i)].
(** Source for [prefix_retraction_linear]: Federer (1969), 1.3.2, pp. 14-15,
    basis e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma prefix_retraction_linear n : linear (@prefix_retraction n).
Proof.
move=> a x y; apply/ffunP=> i.
by rewrite /prefix_retraction !ffunE linearP free_addE free_scaleE.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build K V (coordinate_space K n)
  *:%R (@prefix_retraction n) (@prefix_retraction_linear n).
(** Source for [prefix_inclusionE]: Federer (1969), 1.3.2, pp. 14-15, basis
    e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma prefix_inclusionE n (i : 'I_n) : prefix_inclusion (coordinate_basis K i) = e (val i).
Proof.
change (basis_synthesis (fun j : 'I_n => e (val j))
  (coordinate_to_free (coordinate_basis K i)) = e (val i)).
by rewrite -coordinate_from_free_delta coordinate_from_freeK basis_synthesisE.
Qed.
(** Source for [prefix_retractionE]: Federer (1969), 1.3.2, pp. 14-15, basis
    e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma prefix_retractionE n (i : 'I_n) : prefix_retraction n (e (val i)) = coordinate_basis K i.
Proof.
apply/ffunP=> j; rewrite /prefix_retraction /coordinate_basis !ffunE basis_coordinatesE deltaE.
by rewrite (inj_eq val_inj).
Qed.
(** Source for [prefix_inclusionK]: Federer (1969), 1.3.2, pp. 14-15, basis
    e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma prefix_inclusionK n : cancel (@prefix_inclusion n) (@prefix_retraction n).
Proof.
apply: (basis_linear_ext (coordinate_basisP K n)
  (linear_comp (GRing.Linear.clone _ _ _ _ (@prefix_retraction n) _) (@prefix_inclusion n))
  (linear_id (coordinate_space K n))) => i.
change (prefix_retraction n (prefix_inclusion (coordinate_basis K i)) = coordinate_basis K i).
by rewrite prefix_inclusionE prefix_retractionE.
Qed.

(** Source for [prefix_eventually]: Federer (1969), 1.3.2, pp. 14-15, basis
    e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma prefix_eventually v : exists N, forall n, (N <= n)%N ->
  prefix_inclusion (prefix_retraction n v) = v.
Proof.
elim/(basis_induction he): v => [|x y [N hN] [M hM]|a x [N hN]|i].
- exists 0%N => n _; by rewrite !linear0.
- exists (maxn N M) => n; rewrite geq_max => /andP [hn hm].
  by rewrite !linearD hN // hM.
- exists N => n hn; by rewrite !linearZ hN.
- exists i.+1 => n hn.
  have hi : e i = e (val (Ordinal hn)) by [].
  by rewrite hi prefix_retractionE prefix_inclusionE.
Qed.

(** Source for [exterior_prefix_projection]: Federer (1969), 1.3.2, pp.
    14-15, basis e_1,e_2,e_3,... and increasing m-term products. In words:
    For a countable ordered basis, its increasing m-fold exterior products
    form a basis of the m-th exterior power. Definition or construction used
    to formalise this passage. *)
Definition exterior_prefix_projection n : algebra_map (exterior_algebra V) (exterior_algebra V) :=
  algebra_comp (exterior_algebra_map (prefix_inclusion (n:=n)))
    (exterior_algebra_map (GRing.Linear.clone _ _ _ _ (@prefix_retraction n) _)).
(** Source for [exterior_prefix_projectionE]: Federer (1969), 1.3.2, pp.
    14-15, basis e_1,e_2,e_3,... and increasing m-term products. In words:
    For a countable ordered basis, its increasing m-fold exterior products
    form a basis of the m-th exterior power. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma exterior_prefix_projectionE n v :
  exterior_prefix_projection n (exterior_generator v) =
  exterior_generator (prefix_inclusion (prefix_retraction n v)).
Proof.
change (exterior_algebra_map (prefix_inclusion (n:=n))
  (exterior_algebra_map (GRing.Linear.clone _ _ _ _ (@prefix_retraction n) _)
    (exterior_generator v)) = exterior_generator (prefix_inclusion (prefix_retraction n v))).
by rewrite !exterior_algebra_mapE.
Qed.
(** Source for [exterior_prefix_eventually]: Federer (1969), 1.3.2, pp.
    14-15, basis e_1,e_2,e_3,... and increasing m-term products. In words:
    For a countable ordered basis, its increasing m-fold exterior products
    form a basis of the m-th exterior power. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma exterior_prefix_eventually x : exists N, forall n, (N <= n)%N ->
  exterior_prefix_projection n x = x.
Proof.
elim/exterior_algebra_induction: x => [|x y [N hN] [M hM]|a x [N hN]| |v|x y [N hN] [M hM]].
- exists 0%N => n _; exact: linear0.
- exists (maxn N M) => n; rewrite geq_max => /andP [hn hm].
  rewrite linearD; change (exterior_prefix_projection n x + exterior_prefix_projection n y = x + y).
  by rewrite hN // hM.
- exists N => n hn; rewrite linearZ.
  change (a *: exterior_prefix_projection n x = a *: x); by rewrite hN.
- exists 0%N => n _; exact: (algebra_map_one (exterior_prefix_projection n)).
- have [N hN] := prefix_eventually v; exists N => n hn.
  by rewrite exterior_prefix_projectionE hN.
- exists (maxn N M) => n; rewrite geq_max => /andP [hn hm].
  change (exterior_prefix_projection n (alg_mul (exterior_algebra V) x y) = wedge x y).
  apply: eq_trans (@algebra_map_mul K (exterior_algebra V) (exterior_algebra V)
    (exterior_prefix_projection n) x y) _.
  by rewrite hN // hM.
Qed.

(** Source for [exterior_prefix_spans]: Federer (1969), 1.3.2, pp. 14-15,
    basis e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma exterior_prefix_spans m (x : exterior_power V m) :
  exists n (y : exterior_power (coordinate_space K n) m),
    exterior_power_map (prefix_inclusion (n:=n)) m y = x.
Proof.
have [n hn] := exterior_prefix_eventually (component_val x).
exists n, (exterior_power_map (GRing.Linear.clone _ _ _ _ (@prefix_retraction n) _) m x).
apply: val_inj; exact: hn (leqnn n).
Qed.
End InitialSpans.

(** Federer 1.3.2: all increasing m-termed sequences of positive indices.
    As for Lambda(n,m), the ordinal/natural index i denotes Federer's i+1. *)
(** Source for [Lambda_infty]: Federer (1969), 1.3.2, pp. 14-15, basis
    e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Definition or construction used to
    formalise this passage. *)
Definition Lambda_infty m := {t : m.-tuple nat | sorted ltn t}.
HB.instance Definition _ m := Choice.copy (Lambda_infty m)
  {t : m.-tuple nat | sorted ltn t}.
(** Source for [Lambda_prefix]: Federer (1969), 1.3.2, pp. 14-15, basis
    e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Definition or construction used to
    formalise this passage. *)
Definition Lambda_prefix n m (t : Lambda n m) : Lambda_infty m :=
  Sub [tuple of map val (val t)] (valP t).
(** Source for [Lambda_prefix_injective]: Federer (1969), 1.3.2, pp. 14-15,
    basis e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Lambda_prefix_injective n m : injective (@Lambda_prefix n m).
Proof.
move=> s t h; apply: val_inj; apply: val_inj; apply: (inj_map val_inj).
move: (congr1 (fun x : Lambda_infty m => val (val x)) h).
by rewrite /Lambda_prefix /=.
Qed.

Section RestrictIndices.
Variable m n : nat.
Variable t : Lambda_infty m.
Hypothesis ht : forall i : 'I_m, (tnth (val t) i < n)%N.
(** Source for [Lambda_restriction_tuple]: Federer (1969), 1.3.2, pp. 14-15,
    basis e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Definition or construction used to
    formalise this passage. *)
Definition Lambda_restriction_tuple : m.-tuple 'I_n := [tuple Ordinal (ht i) | i < m].
(** Source for [Lambda_restriction_tupleK]: Federer (1969), 1.3.2, pp.
    14-15, basis e_1,e_2,e_3,... and increasing m-term products. In words:
    For a countable ordered basis, its increasing m-fold exterior products
    form a basis of the m-th exterior power. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma Lambda_restriction_tupleK :
  [tuple of map val Lambda_restriction_tuple] = val t.
Proof. by apply: eq_from_tnth => i; rewrite tnth_map tnth_mktuple. Qed.
(** Source for [Lambda_restriction_sorted]: Federer (1969), 1.3.2, pp.
    14-15, basis e_1,e_2,e_3,... and increasing m-term products. In words:
    For a countable ordered basis, its increasing m-fold exterior products
    form a basis of the m-th exterior power. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma Lambda_restriction_sorted : sorted ltn (map val Lambda_restriction_tuple).
Proof.
have h := valP t.
rewrite -(Lambda_restriction_tupleK) in h; exact: h.
Qed.
(** Source for [Lambda_restriction]: Federer (1969), 1.3.2, pp. 14-15, basis
    e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Definition or construction used to
    formalise this passage. *)
Definition Lambda_restriction : Lambda n m := Sub Lambda_restriction_tuple Lambda_restriction_sorted.
(** Source for [Lambda_restrictionK]: Federer (1969), 1.3.2, pp. 14-15,
    basis e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Lambda_restrictionK : Lambda_prefix Lambda_restriction = t.
Proof. apply: val_inj; exact: Lambda_restriction_tupleK. Qed.
End RestrictIndices.

(** Source for [Lambda_prefix_eventually]: Federer (1969), 1.3.2, pp. 14-15,
    basis e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Lambda_prefix_eventually m (t : Lambda_infty m) :
  exists N, forall n, (N <= n)%N -> exists s : Lambda n m, Lambda_prefix s = t.
Proof.
exists (\max_(i < m) (tnth (val t) i).+1)%N => n hn.
have ht : forall i : 'I_m, (tnth (val t) i < n)%N.
  move=> i; exact: leq_trans (leq_bigmax i) hn.
exists (Lambda_restriction ht); exact: Lambda_restrictionK.
Qed.

Section FiniteSupport.
Variable K : fieldType.
Variable m : nat.
Local Notation F := (GRing.Lmodule.clone K (free_vector K (Choice.clone (Lambda_infty m) _)) _).
(** Source for [Lambda_coefficients_eventually]: Federer (1969), 1.3.2, pp.
    14-15, basis e_1,e_2,e_3,... and increasing m-term products. In words:
    For a countable ordered basis, its increasing m-fold exterior products
    form a basis of the m-th exterior power. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma Lambda_coefficients_eventually (c : F) :
  exists N, forall n, (N <= n)%N ->
    exists d : free_vector K (Choice.clone (Lambda n m) _), free_map K (@Lambda_prefix n m) d = c.
Proof.
elim/free_induction: c => [|x y [N hN] [M hM]|a x [N hN]|t].
- exists 0%N => n _; exists 0; exact: linear0.
- exists (maxn N M) => n; rewrite geq_max => /andP [hn hm].
  have [u hu] := hN n hn; have [v hv] := hM n hm.
  exists (u + v); by rewrite linearD hu hv.
- exists N => n hn; have [u hu] := hN n hn.
  exists (a *: u); by rewrite linearZ hu.
- have [N hN] := Lambda_prefix_eventually t; exists N => n hn.
  have [s hs] := hN n hn; exists (delta K s); by rewrite free_mapE hs.
Qed.
End FiniteSupport.

(** Federer 1.3.2, basis assertion for e_1,e_2,e_3,... . Spanning and
    independence are both reduced to a finite initial span, so no assertion
    about an infinite basis is assumed in the finite-dimensional proof. *)
Section CountableBasis.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variable V : lmodType K.
Variable e : nat -> V.
Hypothesis he : is_basis e.
Variable m : nat.
(** Source for [countable_e_lambda]: Federer (1969), 1.3.2, pp. 14-15, basis
    e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Definition or construction used to
    formalise this passage. *)
Definition countable_e_lambda (t : Lambda_infty m) := e_lambda e (val t).
Local Notation inc n := (@prefix_inclusion K V e n) (only parsing).
Local Notation ret n := (GRing.Linear.clone _ _ _ _ (@prefix_retraction K V e he n) _) (only parsing).

(** Source for [countable_e_lambda_prefix]: Federer (1969), 1.3.2, pp.
    14-15, basis e_1,e_2,e_3,... and increasing m-term products. In words:
    For a countable ordered basis, its increasing m-fold exterior products
    form a basis of the m-th exterior power. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma countable_e_lambda_prefix n (t : Lambda n m) :
  countable_e_lambda (Lambda_prefix t) =
  exterior_power_map (inc n) m (coordinate_e_lambda K t).
Proof.
apply: val_inj.
change (exterior_word [seq e i | i <- map val (val t)] =
  exterior_algebra_map (inc n) (exterior_word [seq @coordinate_basis K n i | i <- val t])).
rewrite exterior_algebra_map_word -!map_comp.
congr 1 (exterior_word _); apply: eq_map => i.
symmetry; exact: prefix_inclusionE.
Qed.

(** Source for [countable_synthesis_prefix]: Federer (1969), 1.3.2, pp.
    14-15, basis e_1,e_2,e_3,... and increasing m-term products. In words:
    For a countable ordered basis, its increasing m-fold exterior products
    form a basis of the m-th exterior power. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma countable_synthesis_prefix n c :
  basis_synthesis countable_e_lambda (free_map K (@Lambda_prefix n m) c) =
  exterior_power_map (inc n) m (basis_synthesis (@coordinate_e_lambda K n m) c).
Proof.
apply: (free_linear_ext
  (linear_comp (basis_synthesis countable_e_lambda) (free_map K (@Lambda_prefix n m)))
  (linear_comp (exterior_power_map (inc n) m) (basis_synthesis (@coordinate_e_lambda K n m)))) c => t.
change (basis_synthesis countable_e_lambda (free_map K (@Lambda_prefix n m) (delta K t)) =
  exterior_power_map (inc n) m (basis_synthesis (@coordinate_e_lambda K n m) (delta K t))).
by rewrite free_mapE !basis_synthesisE countable_e_lambda_prefix.
Qed.

(** Source for [countable_e_lambda_spans]: Federer (1969), 1.3.2, pp. 14-15,
    basis e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma countable_e_lambda_spans x : exists c, basis_synthesis countable_e_lambda c = x.
Proof.
have [n [y hy]] := exterior_prefix_spans he x.
rewrite -hy; clear x hy.
elim/(basis_induction (coordinate_e_lambda_basis h2 n m)): y =>
  [|x y [a ha] [b hb]|a x [c hc]|t].
- exists 0; by rewrite !linear0.
- exists (a + b); by rewrite !linearD ha hb.
- exists (a *: c); by rewrite !linearZ hc.
- exists (delta K (Lambda_prefix t)); by rewrite basis_synthesisE countable_e_lambda_prefix.
Qed.

(** Source for [countable_e_lambda_independent]: Federer (1969), 1.3.2, pp.
    14-15, basis e_1,e_2,e_3,... and increasing m-term products. In words:
    For a countable ordered basis, its increasing m-fold exterior products
    form a basis of the m-th exterior power. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma countable_e_lambda_independent : injective (basis_synthesis countable_e_lambda).
Proof.
move=> x y hxy.
have [N hN] := Lambda_coefficients_eventually x.
have [M hM] := Lambda_coefficients_eventually y.
pose n := maxn N M.
have [a ha] := hN n (leq_maxl N M).
have [b hb] := hM n (leq_maxr N M).
have hs : basis_synthesis (@coordinate_e_lambda K n m) a =
    basis_synthesis (@coordinate_e_lambda K n m) b.
  apply: (can_inj (@exterior_power_mapK K (coordinate_space K n) V
    (inc n) (ret n) (@prefix_inclusionK K V e he n) m)).
  by rewrite -!countable_synthesis_prefix ha hb.
have hab := basis_synthesis_injective (coordinate_e_lambda_basis h2 n m) hs.
by rewrite -ha -hb hab.
Qed.

(** Source for [countable_e_lambda_basis]: Federer (1969), 1.3.2, pp. 14-15,
    basis e_1,e_2,e_3,... and increasing m-term products. In words: For a
    countable ordered basis, its increasing m-fold exterior products form a
    basis of the m-th exterior power. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem countable_e_lambda_basis : is_basis countable_e_lambda.
Proof.
apply/basisP; split; [exact: countable_e_lambda_independent | exact: countable_e_lambda_spans].
Qed.
End CountableBasis.
