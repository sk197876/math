(** Federer (1969), 2.7.16, example (4), printed p. 138: "Since {g : det g =
    1} is the commutator subgroup of GL(n, R), chi(g) = 1 whenever det g =
    1." Federer states the group-theoretic fact without proof. Here V is a
    space with an inner product and a finite basis b_1, ..., b_n, GL(V) its
    linear group with the sealed operations of LinearGroupSealed.v, and the
    commutator subgroup is the intersection of all subgroups containing the
    commutators a c a^{-1} c^{-1} (commutator_subgroup). Both inclusions are
    proved (special_linear_commutator). The inclusion of the commutator
    subgroup in {g : det g = 1} follows from det(g h) = det g det h. For the
    converse, a transvection x |-> x + phi(x) v with phi(v) = 0 is a
    commutator: with psi(v) = 1 and D(x) = x + psi(x) v one has D o T = T o
    T o D, whence D T D^{-1} T^{-1} = T (and T = 1 for v = 0). A map h with
    det h = 1 is reduced to 1_V column by column: if h fixes b_1, ..., b_k
    and y = h(b_{k+1}), then some coordinate y_j with j > k is nonzero, and
    at most four transvections fixing b_1, ..., b_k carry y to b_{k+1}; when
    k + 1 = n the coordinate y_n equals det h = 1 (det_fix_all_but_one, by
    the permutation formula of 1.3.4, p. 16). Consequently every
    homomorphism of GL(V) into the multiplicative group R ~ {0} has the
    value 1 at every g with det g = 1 (special_linear_character_unit). The
    local erratum has no entry for this passage of p. 138. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology.
From mathcomp Require Import fingroup perm.
From Federer Require Import InnerProductUP InnerMetric LinearBasis Bilinear FiniteDualDimension Annihilator TensorUP Hom HomInner
  CoefficientCoordinates ExteriorDeterminant ExteriorLeibniz InversionCount EuclideanLinearMaps TopologicalGroupUP
  TopologicalGroupLaws HomSpaceTopology LinearGroupTopology LinearGroupSealed HomHaarCovariance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FixAllButOne.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [permutation_index_one]: the index of the identity
    permutation is 1, Federer 1.3.3, p. 15 (it has no inversions).
    Supporting lemma. *)
Lemma permutation_index_one : FedererPermutation.index K (1%g : 'S_n) = 1.
Proof.
rewrite FedererPermutation.index_inversions (_ : #|_| = 0%N) ?expr0 //.
apply/eqP; rewrite cards_eq0; apply/eqP/setP=> ij; rewrite !inE !perm1.
apply/negbTE/negP=> /andP [h1 h2'].
by move: (ltn_trans h1 h2'); rewrite ltnn.
Qed.

(** Source for [det_fix_all_but_one]: if f fixes every basis vector
    e_i with i <> i_0, then det f = e_{i_0}*(f(e_{i_0})), Federer 1.3.4,
    p. 16, by the permutation formula: every permutation other than the
    identity moves some i <> i_0, and the corresponding product
    vanishes. Supporting lemma for "{g : det g = 1} is the commutator
    subgroup of GL(n, R)", 2.7.16, p. 138. *)
Lemma det_fix_all_but_one (f : {linear V -> V}) (i0 : 'I_n) :
  (forall i, i != i0 -> f (e i) = e i) -> det h2 he f = (dual_basis he i0 (f (e i0)) : K).
Proof.
move=> hf.
pose a := fun i j : 'I_n => (dual_basis he j (f (e i)) : K).
have ha i j : i != i0 -> a i j = if i == j then 1 else 0.
  by move=> hi; rewrite /a (hf i hi) dual_basisE.
rewrite (det_formula h2 he (f := f) (b := a)); last by move=> i; exact: basis_vector_expansion.
rewrite (bigD1 1%g) //= [X in _ + X]big1 ?addr0.
  rewrite permutation_index_one mul1r (bigD1 i0) //= [X in _ * X]big1 ?mulr1; first by rewrite perm1.
  by move=> i hi; rewrite perm1 ha // eqxx.
move=> s hs.
have [i hi] : exists i, s i != i.
  case: (pickP (fun i => s i != i))=> [i hi|h]; first by exists i.
  move: hs; have -> : s = 1%g by apply/permP=> i; rewrite perm1; move/negbFE/eqP: (h i).
  by rewrite eqxx.
have [i' [hi' hsi']] : exists i', i' != i0 /\ s i' != i'.
  case: (eqVneq i i0)=> [hii0|hii0]; last by exists i.
  subst i; exists (s i0); split=> //.
  by apply/negP=> /eqP /perm_inj /eqP; apply/negP.
by rewrite (bigD1 i') //= ha // [i' == _]eq_sym (negbTE hsi') mul0r mulr0.
Qed.

End FixAllButOne.

Section Commutators.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation det := (linear_group_det hB hb).
Local Notation es := (dual_basis hb).
Local Notation h2 := (euclidean_two_nonzero R).

(** Source for [hgl]: the group laws of GL(V), Federer 2.7.16, p. 134,
    used in this section. *)
Let hgl := linear_group_group_laws hG.

(** Source for [commutator]: the commutator a c a^{-1} c^{-1} in
    GL(n, R), as in "the commutator subgroup of GL(n, R)", Federer
    2.7.16, p. 138. Definition. *)
Definition commutator (a c : GL) : GL := mul (mul (mul a c) (inv a)) (inv c).

(** Source for [commutator_subgroup]: "the commutator subgroup of
    GL(n, R)", Federer 2.7.16, p. 138: the intersection of all subgroups
    containing every commutator. Definition by this universal
    property. *)
Definition commutator_subgroup : set GL :=
  [set g | forall S : set GL, is_subgroup mul inv unit S -> (forall a c, S (commutator a c)) -> S g].

(** Source for [commutator_subgroup_subgroup]: the commutator subgroup
    is a subgroup, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma commutator_subgroup_subgroup : is_subgroup mul inv unit commutator_subgroup.
Proof.
split.
- by move=> S hS _; exact: subgroup_unit hS.
- by move=> g h hg hh S hS hc; exact: (subgroup_mul hS (hg S hS hc) (hh S hS hc)).
- by move=> g hg S hS hc; exact: (subgroup_inv hS (hg S hS hc)).
Qed.

(** Source for [commutator_subgroup_commutator]: every commutator
    belongs to the commutator subgroup, Federer 2.7.16, p. 138.
    Supporting lemma. *)
Lemma commutator_subgroup_commutator a c : commutator_subgroup (commutator a c).
Proof. by move=> S _ hc; exact: hc. Qed.

(** Source for [commutator_det]: det(a c a^{-1} c^{-1}) = 1, Federer
    1.3.4, p. 16. Supporting lemma. *)
Lemma commutator_det a c : det (commutator a c) = 1.
Proof.
rewrite /commutator !linear_group_det_mul !linear_group_det_inv.
have ha := linear_group_det_nonzero a; have hc := linear_group_det_nonzero c.
by rewrite (mulrAC (det a)) (mulfV ha) mul1r (mulfV hc).
Qed.

(** Source for [commutator_subgroup_det]: members of the commutator
    subgroup have determinant 1, Federer 2.7.16, p. 138, the inclusion
    of the commutator subgroup in {g : det g = 1}. Supporting lemma:
    {g : det g = 1} is a subgroup containing every commutator. *)
Lemma commutator_subgroup_det g : commutator_subgroup g -> det g = 1.
Proof.
move=> hg; apply: (hg [set x | det x = 1]); last exact: commutator_det.
split.
- exact: linear_group_det_unit.
- by move=> x y hx hy; rewrite /= linear_group_det_mul hx hy mulr1.
- by move=> x hx; rewrite /= linear_group_det_inv hx invr1.
Qed.

(** Source for [linear_group_ext]: members of GL(V) with the same values
    on the basis are equal, Federer 1.1.2, p. 10. Supporting lemma. *)
Lemma linear_group_ext (g h : GL) : (forall i, (set_val g : Hom V V) (b i) = (set_val h : Hom V V) (b i)) -> g = h.
Proof.
move=> he; apply: val_inj; rewrite /= -!set_valE; apply: hom_ext.
exact: (basis_linear_ext hb (hom_as_linear (set_val g : Hom V V)) (hom_as_linear (set_val h : Hom V V)) he).
Qed.

(** Source for [linear_group_mul_apply]: (g h)(x) = g(h(x)), Federer
    2.7.16, p. 134. Supporting lemma. *)
Lemma linear_group_mul_apply (g h : GL) x :
  (set_val (mul g h) : Hom V V) x = (set_val g : Hom V V) ((set_val h : Hom V V) x).
Proof. by rewrite (linear_group_mulE hG) hom_compE. Qed.

(** Source for [linear_group_unit_apply]: 1_V(x) = x, Federer 2.7.16,
    p. 134. Supporting lemma. *)
Lemma linear_group_unit_apply x : (set_val unit : Hom V V) x = x.
Proof. by rewrite (linear_group_unitE hG). Qed.

Section Transvection.
Variable phi : Hom V R^o.
Variable v : V.

(** Source for [rank_one_shift]: the map x |-> x + phi(x) v of V,
    supporting the transvections used for "the commutator subgroup of
    GL(n, R)", Federer 2.7.16, p. 138. Definition. *)
Definition rank_one_shift : Hom V V := hom_identity V + hom_with_coefficient v phi.

(** Source for [rank_one_shiftE]: the values x + phi(x) v, Federer
    2.7.16, p. 138. Supporting lemma. *)
Lemma rank_one_shiftE x : rank_one_shift x = x + (phi x : R) *: v.
Proof. by rewrite hom_addE hom_identityE hom_with_coefficientE. Qed.

(** Source for [rank_one_shift_injective]: x |-> x + phi(x) v is
    univalent when phi(v) <> -1, Federer 2.7.16, p. 138: phi(x) is
    recovered from (1 + phi(v)) phi(x). Supporting lemma. *)
Lemma rank_one_shift_injective : (phi v : R) + 1 != 0 -> injective rank_one_shift.
Proof.
move=> hv x y; rewrite !rank_one_shiftE=> hxy.
have hl (z : V) : (phi (z + (phi z : R) *: v) : R) = (phi z : R) * ((phi v : R) + 1).
  by rewrite (linD (hom_linear _)) (linZ (hom_linear _)) mulrDr mulr1 addrC.
have hp : (phi x : R) = phi y.
  by apply: (mulIf hv); rewrite -!hl hxy.
by move: hxy; rewrite hp=> /addIr.
Qed.

End Transvection.

(** Source for [transvection_injective]: x |-> x + phi(x) v with
    phi(v) = 0 is univalent, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma transvection_injective (phi : Hom V R^o) (v : V) (h : (phi v : R) = 0) : injective (rank_one_shift phi v).
Proof. by apply: rank_one_shift_injective; rewrite h add0r oner_neq0. Qed.

(** Source for [transvection]: the transvection x |-> x + phi(x) v with
    phi(v) = 0 as a member of GL(V), Federer 2.7.16, p. 138.
    Definition. *)
Definition transvection (phi : Hom V R^o) (v : V) (h : (phi v : R) = 0) : GL :=
  exist _ (rank_one_shift phi v : inner_metric_space (hom_inner_productP hB hB hb))
    (mem_set (transvection_injective h)).

(** Source for [transvectionE]: the values of a transvection, Federer
    2.7.16, p. 138. Supporting lemma. *)
Lemma transvectionE (phi : Hom V R^o) (v : V) (h : (phi v : R) = 0) x :
  (set_val (transvection h) : Hom V V) x = x + (phi x : R) *: v.
Proof. exact: rank_one_shiftE. Qed.

(** Source for [transvection_commutator]: every transvection is a
    commutator in GL(V), supporting "{g : det g = 1} is the commutator
    subgroup of GL(n, R)", Federer 2.7.16, p. 138. Supporting lemma:
    for v <> 0 choose psi with psi(v) = 1 and D(x) = x + psi(x) v;
    then D o T = T o T o D, so D T D^{-1} T^{-1} = T; for v = 0,
    T = 1 = 1 1 1^{-1} 1^{-1}. *)
Lemma transvection_commutator (phi : Hom V R^o) (v : V) (h : (phi v : R) = 0) :
  commutator_subgroup (transvection h).
Proof.
have [hv0|hv0] := eqVneq v 0.
  have -> : transvection h = unit.
    apply: linear_group_ext=> i; rewrite transvectionE linear_group_unit_apply hv0.
    by rewrite scaler0 addr0.
  exact: (subgroup_unit commutator_subgroup_subgroup).
have [j hj] : exists j, (es j v : R) != 0.
  apply/existsP; move: hv0; apply: contraNT=> /existsPn hall.
  apply/eqP; rewrite (basis_vector_expansion hb v) big1 // => j _.
  by move/negbNE/eqP: (hall j)=> ->; rewrite scale0r.
pose psi : Hom V R^o := (es j v : R)^-1 *: es j.
have hpsi : (psi v : R) = 1 by rewrite hom_scaleE; exact: (mulVf hj).
have hD : (psi v : R) + 1 != 0 by rewrite hpsi; exact: euclidean_two_nonzero.
pose D : GL := exist _ (rank_one_shift psi v : inner_metric_space (hom_inner_productP hB hB hb))
  (mem_set (rank_one_shift_injective hD)).
have hDE x : (set_val D : Hom V V) x = x + (psi x : R) *: v by exact: rank_one_shiftE.
pose T := transvection h.
have hTT : mul D T = mul (mul T T) D.
  apply: linear_group_ext=> i; rewrite !linear_group_mul_apply.
  rewrite [in LHS]hDE [in RHS]hDE !transvectionE.
  rewrite !(linD (hom_linear _)) !(linZ (hom_linear _)) h hpsi !scaler0 !addr0.
  rewrite (_ : ((phi (b i) : R^o)%:A : R^o) = phi (b i)); last exact: mulr1.
  rewrite scalerDl !addrA; congr (_ + _); rewrite -!addrA; congr (_ + _).
  exact: addrC.
suff -> : transvection h = commutator D T by exact: commutator_subgroup_commutator.
rewrite /commutator hTT (group_mulgK hgl).
by rewrite -(group_mulA hgl) (group_mulgV hgl) (group_mulg1 hgl).
Qed.

(** Source for [coordinate_transvection]: the transvection
    x |-> x + e_j*(x) v for v with e_j*(v) = 0 as a member of GL(V),
    Federer 2.7.16, p. 138. Definition. *)
Definition coordinate_transvection (j : 'I_n) (v : V) (h : (es j v : R) = 0) : GL := transvection h.

(** Source for [coordinate_transvection_fixed]: the transvection
    x |-> x + e_j*(x) v fixes e_i for i <> j, Federer 1.1.4, p. 11.
    Supporting lemma. *)
Lemma coordinate_transvection_fixed (j : 'I_n) (v : V) (h : (es j v : R) = 0) i :
  i != j -> (set_val (coordinate_transvection h) : Hom V V) (b i) = b i.
Proof. by move=> hij; rewrite transvectionE dual_basisE (negbTE hij) scale0r addr0. Qed.

(** Source for [coordinate_transvection_commutator]: the transvection
    x |-> x + e_j*(x) v belongs to the commutator subgroup, Federer
    2.7.16, p. 138. Supporting lemma. *)
Lemma coordinate_transvection_commutator (j : 'I_n) (v : V) (h : (es j v : R) = 0) :
  commutator_subgroup (coordinate_transvection h).
Proof. exact: transvection_commutator. Qed.

(** Source for [coordinate_add]: e_j*(x + y) = e_j*(x) + e_j*(y),
    Federer 1.1.4, p. 11. Supporting lemma. *)
Lemma coordinate_add (j : 'I_n) x y : (es j (x + y) : R) = es j x + es j y.
Proof. by rewrite (linD (hom_linear _)). Qed.

(** Source for [coordinate_sub]: e_j*(x - y) = e_j*(x) - e_j*(y),
    Federer 1.1.4, p. 11. Supporting lemma. *)
Lemma coordinate_sub (j : 'I_n) x y : (es j (x - y) : R) = es j x - es j y.
Proof. by rewrite (linB (hom_linear _)). Qed.

(** Source for [coordinate_scale]: e_j*(c x) = c e_j*(x), Federer
    1.1.4, p. 11. Supporting lemma. *)
Lemma coordinate_scale (j : 'I_n) (c : R) x : (es j (c *: x) : R) = c * es j x.
Proof. by rewrite (linZ (hom_linear _)). Qed.

(** Source for [coordinate_basis]: e_j*(e_i) = 1 if i = j and 0
    otherwise, Federer 1.1.4, p. 11. Supporting lemma. *)
Lemma coordinate_basis (j i : 'I_n) : (es j (b i) : R) = if i == j then 1 else 0.
Proof. exact: dual_basisE. Qed.

(** Source for [coordinate_sum]: e_j* of a finite sum, Federer 1.1.4,
    p. 11. Supporting lemma. *)
Lemma coordinate_sum (j : 'I_n) (P : pred 'I_n) (F : 'I_n -> V) :
  (es j (\sum_(i | P i) F i) : R) = \sum_(i | P i) (es j (F i) : R).
Proof.
apply: (big_morph (fun x => (es j x : R)) (@coordinate_add j)).
by rewrite (lin0 (hom_linear _)).
Qed.

(** Source for [coordinate_basis_other]: e_j*(c e_i) = 0 for i <> j,
    Federer 1.1.4, p. 11. Supporting lemma. *)
Lemma coordinate_basis_other (i j : 'I_n) (c : R) : i != j -> (es j (c *: b i) : R) = 0.
Proof. by move=> hij; rewrite coordinate_scale coordinate_basis (negbTE hij) mulr0. Qed.

(** Source for [is_column_reduction]: tau belongs to the commutator
    subgroup and fixes e_1, ..., e_k, supporting the reduction of a
    member of {g : det g = 1} to 1_V, Federer 2.7.16, p. 138.
    Definition. *)
Definition is_column_reduction (k : nat) (tau : GL) : Prop :=
  commutator_subgroup tau /\ forall i : 'I_n, (i < k)%N -> (set_val tau : Hom V V) (b i) = b i.

(** Source for [column_reduction_mul]: products of such maps are such
    maps, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma column_reduction_mul k (s t : GL) : is_column_reduction k s -> is_column_reduction k t ->
  is_column_reduction k (mul s t).
Proof.
move=> [hs hsf] [ht htf]; split; first exact: (subgroup_mul commutator_subgroup_subgroup hs ht).
by move=> i hi; rewrite linear_group_mul_apply htf // hsf.
Qed.

(** Source for [column_reduction_unit]: 1_V is such a map, Federer
    2.7.16, p. 138. Supporting lemma. *)
Lemma column_reduction_unit k : is_column_reduction k unit.
Proof.
split; first exact: (subgroup_unit commutator_subgroup_subgroup).
by move=> i _; rewrite linear_group_unit_apply.
Qed.

(** Source for [column_reduction_transvection]: x |-> x + e_j*(x) v
    with j >= k is such a map, Federer 2.7.16, p. 138. Supporting
    lemma. *)
Lemma column_reduction_transvection k (j : 'I_n) (v : V) (h : (es j v : R) = 0) :
  (k <= j)%N -> is_column_reduction k (coordinate_transvection h).
Proof.
move=> hkj; split; first exact: coordinate_transvection_commutator.
move=> i hi; apply: coordinate_transvection_fixed.
by apply/negP=> /eqP hij; move: hi; rewrite hij ltnNge hkj.
Qed.

(** Source for [column_step]: if y has a nonzero coordinate y_j with
    j >= k, and y_k = 1 in case k + 1 = n, then a member of the
    commutator subgroup fixing e_1, ..., e_k maps y to e_{k+1} (indices
    from 0 in the formal statement), Federer 2.7.16, p. 138. Supporting
    lemma: at most four transvections, one making y_k nonzero, two
    making it 1 and one clearing the other coordinates. *)
Lemma column_step (k : 'I_n) (y : V) :
  (exists2 j : 'I_n, (k <= j)%N & (es j y : R) != 0) -> (k.+1 = n -> (es k y : R) = 1) ->
  exists2 tau, is_column_reduction k tau & (set_val tau : Hom V V) y = b k.
Proof.
move=> [j hkj hj] hlast.
(* first step: a nonzero coordinate at k *)
have [s1 hs1 [hy1 hl1]] : exists2 s1, is_column_reduction k s1 &
    (es k ((set_val s1 : Hom V V) y) : R) != 0 /\
    (k.+1 = n -> (es k ((set_val s1 : Hom V V) y) : R) = 1).
  have [hk|hk] := eqVneq (es k y : R) 0; last first.
    by exists unit; [exact: column_reduction_unit|rewrite linear_group_unit_apply].
  have hkj' : k != j by apply/negP=> /eqP hjk; move: hj; rewrite -hjk hk eqxx.
  exists (coordinate_transvection (coordinate_basis_other 1 hkj'));
    first exact: column_reduction_transvection.
  have he : (es k ((set_val (coordinate_transvection (coordinate_basis_other 1 hkj')) : Hom V V) y) : R)
      = es j y.
    by rewrite transvectionE coordinate_add coordinate_scale scale1r coordinate_basis eqxx hk add0r mulr1.
  rewrite he; split=> // hn.
  by move: (hlast hn); rewrite hk=> /esym /eqP; rewrite oner_eq0.
pose y1 := (set_val s1 : Hom V V) y.
(* second step: the coordinate at k becomes 1 *)
have [s2 hs2 hy2] : exists2 s2, is_column_reduction k s2 & (es k ((set_val s2 : Hom V V) y1) : R) = 1.
  have [h1|h1] := eqVneq (es k y1 : R) 1.
    by exists unit; [exact: column_reduction_unit|rewrite linear_group_unit_apply].
  have hk1 : (k.+1 < n)%N.
    rewrite ltn_neqAle ltn_ord andbT; apply/negP=> /eqP hn.
    by move: h1; rewrite (hl1 hn) eqxx.
  pose k1 : 'I_n := Ordinal hk1.
  have hkk1 : k != k1 by rewrite -val_eqE /= neq_ltn ltnSn.
  pose a := (es k y1 : R).
  pose c1 := (1 - (es k1 y1 : R)) / a.
  have hv2 : (es k (c1 *: b k1) : R) = 0 by apply: coordinate_basis_other; rewrite eq_sym.
  pose t2 := coordinate_transvection hv2.
  have hv3 : (es k1 ((1 - a) *: b k) : R) = 0 by exact: coordinate_basis_other.
  pose t3 := coordinate_transvection hv3.
  exists (mul t3 t2).
    by apply: column_reduction_mul; apply: column_reduction_transvection=> //=; exact: leqnSn.
  rewrite linear_group_mul_apply !transvectionE.
  have e1 : (es k1 (y1 + (es k y1 : R) *: (c1 *: b k1)) : R) = 1.
    rewrite coordinate_add !coordinate_scale coordinate_basis eqxx mulr1 -/a /c1.
    by rewrite [a * _]mulrC (divfK hy1) addrC subrK.
  have e2 : (es k (y1 + (es k y1 : R) *: (c1 *: b k1)) : R) = a.
    rewrite coordinate_add !coordinate_scale coordinate_basis.
    by rewrite [k1 == k]eq_sym (negbTE hkk1) !mulr0 addr0.
  rewrite e1 scale1r coordinate_add e2 coordinate_scale coordinate_basis eqxx mulr1.
  by rewrite addrC subrK.
pose y2 := (set_val s2 : Hom V V) y1.
(* third step: clearing the other coordinates *)
have hv4 : (es k (b k - y2) : R) = 0.
  by rewrite coordinate_sub coordinate_basis eqxx hy2 subrr.
exists (mul (coordinate_transvection hv4) (mul s2 s1)).
  apply: column_reduction_mul; first exact: column_reduction_transvection.
  exact: column_reduction_mul.
rewrite !linear_group_mul_apply -/y1 -/y2 transvectionE hy2 scale1r.
by rewrite addrC subrK.
Qed.

(** Source for [column_reduction_exists]: for every g with det g = 1
    and k <= n there is tau in the commutator subgroup such that tau g
    fixes e_1, ..., e_k, Federer 2.7.16, p. 138. Supporting lemma, by
    induction on k: if h = tau g fixes e_1, ..., e_k and y = h(e_{k+1}),
    then y has a nonzero coordinate y_j with j > k since h is univalent,
    and y_n = det h = 1 when k + 1 = n (det_fix_all_but_one). *)
Lemma column_reduction_exists (g : GL) : det g = 1 ->
  forall k, (k <= n)%N -> exists tau, commutator_subgroup tau /\
    forall i : 'I_n, (i < k)%N -> (set_val (mul tau g) : Hom V V) (b i) = b i.
Proof.
move=> hg; elim=> [|k ih] hk.
  by exists unit; split=> // ; exact: (subgroup_unit commutator_subgroup_subgroup).
have [tau [htau hfix]] := ih (ltnW hk).
pose kk : 'I_n := Ordinal hk.
pose h := mul tau g.
pose y := (set_val h : Hom V V) (b kk).
have hdet : det h = 1 by rewrite /h linear_group_det_mul (commutator_subgroup_det htau) hg mulr1.
have hnz : exists2 j : 'I_n, (kk <= j)%N & (es j y : R) != 0.
  case: (pickP (fun j : 'I_n => (kk <= j)%N && ((es j y : R) != 0)))=> [j /andP [h1 h2]|hall].
    by exists j.
  exfalso.
  pose z := \sum_(i < n | (i < k)%N) (es i y : R) *: b i.
  have hyz : y = z.
    rewrite {1}(basis_vector_expansion hb y) (bigID (fun i : 'I_n => (i < k)%N)) /=.
    rewrite [X in _ + X]big1 ?addr0 // => i hi.
    have hki : (kk <= i)%N by rewrite /= leqNgt.
    by move: (hall i); rewrite /= hki /= => /negbFE /eqP ->; rewrite scale0r.
  have hhz : (set_val h : Hom V V) z = z.
    rewrite /z (big_morph (set_val h : Hom V V) (linD (hom_linear _)) (lin0 (hom_linear _))).
    by apply: eq_bigr=> i hi; rewrite (linZ (hom_linear _)) hfix.
  have hbz : b kk = z by apply: (set_valP h); rewrite -/y hyz hhz.
  have h1 : (es kk (b kk) : R) = es kk z by rewrite -hbz.
  move: h1; rewrite coordinate_basis eqxx /z coordinate_sum big1 => [h10|i hi].
    by move/eqP: h10; rewrite oner_eq0.
  rewrite coordinate_scale coordinate_basis.
  have -> : (i == kk) = false by apply/negP=> /eqP hki; move: hi; rewrite hki ltnn.
  by rewrite mulr0.
have hlast : kk.+1 = n -> (es kk y : R) = 1.
  move=> hn; rewrite -hdet /linear_group_det /hom_det (@det_fix_all_but_one _ h2 _ _ _ hb (hom_as_linear (set_val h : Hom V V)) kk) //.
  move=> i hik; apply: hfix.
  have : (i < k.+1)%N by rewrite hn; exact: ltn_ord.
  rewrite ltnS leq_eqVlt=> /orP [/eqP hik'|//].
  by move: hik; rewrite (_ : i = kk) ?eqxx //; apply: val_inj.
have [t [ht htf] hty] := column_step hnz hlast.
exists (mul t tau); split; first exact: (subgroup_mul commutator_subgroup_subgroup ht htau).
move=> i hi; rewrite -(group_mulA hgl) linear_group_mul_apply.
rewrite ltnS leq_eqVlt in hi; case/orP: hi=> [/eqP hik|hik].
  have -> : i = kk by apply: val_inj.
  exact: hty.
by rewrite hfix // htf.
Qed.

(** Source for [special_linear_commutator]: "{g : det g = 1} is the
    commutator subgroup of GL(n, R)", Federer 2.7.16, p. 138, for the
    linear group of V. Direct formalisation; Federer gives no proof. *)
Theorem special_linear_commutator (g : GL) : det g = 1 <-> commutator_subgroup g.
Proof.
split; last exact: commutator_subgroup_det.
move=> hg; have [tau [htau hfix]] := column_reduction_exists hg (leqnn n).
have he : mul tau g = unit.
  by apply: linear_group_ext=> i; rewrite hfix // linear_group_unit_apply.
have -> : g = inv tau.
  by rewrite -[g](group_mulKg hgl tau) he (group_mulg1 hgl).
exact: (subgroup_inv commutator_subgroup_subgroup htau).
Qed.

(** Source for [special_linear_character_unit]: "chi(g) = 1 whenever
    det g = 1", Federer 2.7.16, p. 138, for every homomorphism chi of
    GL(n, R) into the multiplicative group R ~ {0}: the set
    {g : chi(g) = 1} is a subgroup containing every commutator, hence
    contains {g : det g = 1} by special_linear_commutator. Direct
    formalisation; continuity of chi is not needed. *)
Corollary special_linear_character_unit (chi : GL -> R) :
  (forall g h, chi (mul g h) = chi g * chi h) -> (forall g, chi g != 0) ->
  forall g, det g = 1 -> chi g = 1.
Proof.
move=> hM h0 g /special_linear_commutator hg.
have hu : chi unit = 1.
  apply: (mulfI (h0 unit)); rewrite -hM (group_mulg1 hgl); exact: (esym (mulr1 _)).
have hinv x : chi (inv x) = (chi x)^-1.
  apply: (mulIf (h0 x)); rewrite -hM (group_mulVg hgl) hu mulVf //.
apply: (hg [set x | chi x = 1]).
- split.
  + exact: hu.
  + by move=> x y hx hy; rewrite /= hM hx hy mulr1.
  + by move=> x hx; rewrite /= hinv hx invr1.
- move=> a c; rewrite /commutator /= !hM !hinv.
  by rewrite (mulrAC (chi a)) (mulfV (h0 a)) mul1r (mulfV (h0 c)).
Qed.

End Commutators.

Arguments commutator {R V B} hB {n b} hb a c.
Arguments commutator_subgroup {R V B} hB {n b} hb g.
