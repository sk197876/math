(** Federer (1969), 2.7.16, example (4), printed p. 138: "the action of
    GL(n, R) on the space of all nonzero simple m vectors of R^n". Federer
    presupposes that this space is a homogeneous space of GL(n, R) in the
    sense of 2.7.1, p. 121. This module supplies the algebra used for the
    openness of the orbit maps: a product of m vectors scaled by d_1, ...,
    d_m is multiplied by d_1 ... d_m (1.3.4, p. 16, through the expansion
    exterior_Leibniz); a product of an orthonormal family has norm 1 (1.7.5,
    pp. 31–32, the permutation formula); every simple m-vector of norm 1 is
    the product of an orthonormal family (Gram–Schmidt in its associated
    subspace, 1.7.1, p. 28, and a change of sign of one factor); and two
    orthonormal families of m vectors correspond under an orthogonal map of
    V (1.7.2, p. 28, OrthogonalInjectionSpaces.v). For m = 0 the last two
    facts are not needed, and the module assumes 0 < m where it uses a
    factor. The local erratum has no entry for this passage. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import fingroup perm.
From Federer Require Import RealMetricBackground InnerProductUP InnerProductLaws InnerNorm InnerMetric
  InnerNormedTopology LinearBasis Bilinear InversionCount GradedComponents TensorUP Hom HomInner
  FiniteDualDimension Annihilator ModuleQuotient SubspaceCarrier GrassmannSubspaces InnerProductRestriction
  ExteriorGrading ExteriorAlgebra ExteriorMaps FiniteExteriorPowers ExteriorMapScaling ExteriorLeibniz
  InnerExterior InnerExteriorProducts InnerExteriorPositivity ExteriorNorm AssociatedSubspace SimpleElementary
  SimpleDimensionCriterion OrthonormalFamilies OrthonormalisationUP GramSchmidt OrthogonalMaps
  OrthogonalBasisCriteria BasisInterpolation EuclideanInnerProduct FiniteCoordinates GrassmannAbbreviations
  EuclideanLinearMaps CoordinateProjection HomSpaceTopology OrthogonalGroupTopology OrthogonalInjectionSpaces
  SpecialLinearCommutators SimpleVectorAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section DiagonalSums.
Variable K : fieldType.
Variable m : nat.

(** Source for [diagonal_permutation_sum]: for a with a(i, j) = 0 when
    i <> j, sum_s index(s) prod_i a(i, s(i)) = prod_i a(i, i), Federer
    1.3.4, p. 16: every permutation other than the identity moves some
    i. Supporting lemma for 2.7.16, p. 138. *)
Lemma diagonal_permutation_sum (a : 'I_m -> 'I_m -> K) :
  (forall i j, i != j -> a i j = 0) ->
  \sum_(s : 'S_m) FedererPermutation.index K s * \prod_(i < m) a i (s i) = \prod_(i < m) a i i.
Proof.
move=> ha.
rewrite (bigD1 1%g) //= [X in _ + X]big1 ?addr0.
  rewrite permutation_index_one mul1r; apply: eq_bigr=> i _; by rewrite perm1.
move=> s hs.
have [i hi] : exists i, s i != i.
  case: (pickP (fun i => s i != i))=> [i hi|h]; first by exists i.
  move: hs; have -> : s = 1%g by apply/permP=> i; rewrite perm1; move/negbFE/eqP: (h i).
  by rewrite eqxx.
by rewrite (bigD1 i) //= ha 1?eq_sym // mul0r mulr0.
Qed.

End DiagonalSums.

Section WordScaling.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.

(** Source for [word_diagonal_scale]: (d_1 v_1) wedge ... wedge
    (d_m v_m) = (d_1 ... d_m) v_1 wedge ... wedge v_m, Federer 1.3.4,
    p. 16 (multilinearity of the exterior product, through
    exterior_Leibniz). Supporting lemma for 2.7.16, p. 138. *)
Lemma word_diagonal_scale (u : 'I_m -> V) (d : 'I_m -> K) :
  e_lambda (fun i => d i *: u i) (ord_tuple m) = (\prod_(i < m) d i) *: e_lambda u (ord_tuple m).
Proof.
pose a := fun i j : 'I_m => if i == j then d i else 0.
have hsum i : \sum_(j < m) a i j *: u j = d i *: u i.
  rewrite (bigD1 i) //= big1 ?addr0; first by rewrite /a eqxx.
  by move=> j hj; rewrite /a eq_sym (negbTE hj) scale0r.
have hdiag : \sum_(s : 'S_m) FedererPermutation.index K s * \prod_(i < m) a i (s i) = \prod_(i < m) d i.
  rewrite diagonal_permutation_sum; last by move=> i j hij; rewrite /a (negbTE hij).
  by apply: eq_bigr=> i _; rewrite /a eqxx.
apply: val_inj.
change (component_val (e_lambda (fun i => d i *: u i) (ord_tuple m)) =
  component_val ((\prod_(i < m) d i) *: e_lambda u (ord_tuple m))).
rewrite e_lambdaE val_ord_tuple.
have -> : [seq d i *: u i | i <- enum 'I_m] = [seq \sum_(j < m) a i j *: u j | i <- enum 'I_m].
  by apply: eq_map=> i; rewrite hsum.
rewrite exterior_Leibniz hdiag.
by rewrite linearZ.
Qed.

End WordScaling.

Section WordChange.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.

(** Source for [word_change_basis]: (sum_j a_1j u_j) wedge ... wedge
    (sum_j a_mj u_j) = (sum_s index(s) prod_i a_{i s(i)}) u_1 wedge ...
    wedge u_m, Federer 1.3.4, p. 16 (exterior_Leibniz). Supporting lemma
    for 2.7.16, p. 138. *)
Lemma word_change_basis (u : 'I_m -> V) (a : 'I_m -> 'I_m -> K) :
  e_lambda (fun i => \sum_(j < m) a i j *: u j) (ord_tuple m) =
    (\sum_(s : 'S_m) FedererPermutation.index K s * \prod_(i < m) a i (s i)) *: e_lambda u (ord_tuple m).
Proof.
apply: val_inj.
change (component_val (e_lambda (fun i => \sum_(j < m) a i j *: u j) (ord_tuple m)) =
  component_val ((\sum_(s : 'S_m) FedererPermutation.index K s * \prod_(i < m) a i (s i)) *:
    e_lambda u (ord_tuple m))).
rewrite e_lambdaE val_ord_tuple exterior_Leibniz.
by rewrite linearZ.
Qed.

End WordChange.

Section OrthonormalWords.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.
Local Notation h2 := (euclidean_two_nonzero R).
Local Notation L := (inner_metric_space (exterior_inner_productP h2 hB m)).

(** Source for [orthonormal_word_inner]: u_1 wedge ... wedge u_m has
    inner square 1 for an orthonormal family u, Federer 1.7.5, pp.
    31–32, by the permutation formula. Supporting lemma for 2.7.16,
    p. 138. *)
Lemma orthonormal_word_inner (u : 'I_m -> V) : orthonormal_family B u ->
  exterior_inner_form h2 hB (e_lambda u (ord_tuple m)) (e_lambda u (ord_tuple m)) = 1.
Proof.
move=> hu; rewrite (exterior_inner_product_permutations h2 hB).
have hf (s : 'S_m) : foldr *%R 1 [seq B (u (s i)) (u i) | i <- enum 'I_m] = \prod_(i < m) B (u (s i)) (u i).
  by rewrite foldrE big_map enumT.
under eq_bigr do rewrite hf.
rewrite (diagonal_permutation_sum (a := fun i j => B (u j) (u i))); last first.
  by move=> i j hij; rewrite hu eq_sym (negbTE hij).
by rewrite big1 // => i _; rewrite hu eqxx.
Qed.

(** Source for [orthonormal_word_norm]: |u_1 wedge ... wedge u_m| = 1
    for an orthonormal family u, Federer 1.7.5, p. 32. Supporting
    lemma. *)
Lemma orthonormal_word_norm (u : 'I_m -> V) : orthonormal_family B u -> `|(e_lambda u (ord_tuple m) : L)| = 1.
Proof.
move=> hu; rewrite inner_norm_topologyE; apply: inner_norm_value; first exact: ler01.
by rewrite expr1n (orthonormal_word_inner hu).
Qed.

Hypothesis hm : (0 < m)%N.

(** Source for [unit_simple_frame]: a simple m-vector of norm 1 is the
    product of an orthonormal family, Federer 1.6.1, p. 24, 1.7.1,
    p. 28, and 1.7.5, p. 32: with a basis w of the associated subspace
    and an orthonormal basis o of it, w_1 wedge ... wedge w_m =
    c o_1 wedge ... wedge o_m with |c| = 1; for c = -1 the sign of o_1
    is changed. Supporting lemma for 2.7.16, p. 138. *)
Lemma unit_simple_frame (x : L) : `|x| = 1 -> simple x ->
  exists u : 'I_m -> V, orthonormal_family B u /\ x = e_lambda u (ord_tuple m).
Proof.
move=> hx1 hs.
have hx0 : x != 0 by apply/eqP=> h0; move: hx1; rewrite h0 normr0=> /esym /eqP; rewrite oner_eq0.
have [W [w [hw hxw]]] := nonzero_simple_frame (conj hx0 hs).
have hBW := restricted_inner_productP hB W.
have [o [ho hgs]] := orthonormal_basis_exists hBW hw.
have hoo := orthonormalisation_orthonormal hgs.
pose u0 := fun i => subspace_val (o i).
have hu0 : orthonormal_family B u0 by move=> i j; exact: hoo i j.
pose a := fun i j => (dual_basis ho j (w i) : R).
have hwexp i : subspace_val (w i) = \sum_(j < m) a i j *: u0 j.
  rewrite {1}(basis_vector_expansion ho (w i)) linear_sum.
  by apply: eq_bigr=> j _; rewrite linearZ.
pose c := \sum_(s : 'S_m) FedererPermutation.index R s * \prod_(i < m) a i (s i).
have hxc : x = c *: e_lambda u0 (ord_tuple m).
  rewrite hxw -word_change_basis; apply: (congr1 (fun e : 'I_m -> V => e_lambda e (ord_tuple m))).
  by apply: funext=> i; rewrite hwexp.
have hc1 : `|c| = 1.
  by move: hx1; rewrite hxc normrZ (orthonormal_word_norm hu0) mulr1.
pose i0 : 'I_m := Ordinal hm.
have [hcp|hcn] := ger0P c.
  exists u0; split=> //; rewrite hxc.
  have -> : c = 1 by rewrite -hc1 (ger0_norm hcp).
  by rewrite scale1r.
pose d := fun i : 'I_m => if i == i0 then -1 else 1 : R.
exists (fun i => d i *: u0 i); split.
  move=> i j; rewrite (bilZl (inner_bilinear hB)) (bilZr (inner_bilinear hB)) hu0 /d.
  case: (eqVneq i j)=> [<-|hij]; last by rewrite !scaler0.
  rewrite /d; case: (i == i0); first by rewrite !scaleN1r opprK.
  by rewrite !scale1r.
rewrite word_diagonal_scale hxc.
have -> : \prod_(i < m) d i = -1.
  rewrite (bigD1 i0) //= big1 ?mulr1; first by rewrite /d eqxx.
  by move=> i hi; rewrite /d (negbTE hi).
have -> : c = -1 by rewrite -[c]opprK -(ltr0_norm hcn) hc1.
by [].
Qed.

End OrthonormalWords.

Section OrthonormalFrames.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable m : nat.

(** Source for [orthonormal_frames_orthogonal]: two orthonormal
    families of m vectors correspond under an orthogonal map of V,
    Federer 1.7.2, p. 28, as used for the transitivity of O(n) on the
    simple m-vectors of norm 1, 2.7.16, p. 138. Supporting lemma, by
    orthogonal_injection_transitive for R^m with the standard basis. *)
Lemma orthonormal_frames_orthogonal (u u' : 'I_m -> V) :
  orthonormal_family B u -> orthonormal_family B u' ->
  exists s : {linear V -> V}, is_orthogonal_map B B s /\ forall i, s (u i) = u' i.
Proof.
move=> hu hu'.
have hC := @euclidean_inner_productP R m.
have hc := @coordinate_basisP R m.
have hoc : orthonormal_family (euclidean_inner_product (n := m)) (FiniteCoordinates.coordinate_basis R (n := m)).
  by move=> i j; rewrite euclidean_inner_basis /FiniteCoordinates.coordinate_basis ffunE eq_sym.
pose f1 := basis_interpolation hc u.
pose f2 := basis_interpolation hc u'.
have hf1 : is_orthogonal_map (euclidean_inner_product (n := m)) B f1.
  apply: (orthogonal_map_basis_criterion hC hB hc hoc)=> i j.
  by rewrite /f1 !basis_interpolationE; exact: hu.
have hf2 : is_orthogonal_map (euclidean_inner_product (n := m)) B f2.
  apply: (orthogonal_map_basis_criterion hC hB hc hoc)=> i j.
  by rewrite /f2 !basis_interpolationE; exact: hu'.
have [s [hs hsf]] := orthogonal_injection_transitive hC hB hc hb hf1 hf2.
exists s; split=> // i.
by have := hsf (FiniteCoordinates.coordinate_basis R (n := m) i); rewrite /f1 /f2 !basis_interpolationE.
Qed.

End OrthonormalFrames.
