(** Private existence machinery for Federer (1969), 2.10.38, printed pp.
    198–199. Implement successive perpendicular projections in the original
    Euclidean space, rather than repeatedly renaming coordinates in a
    lower-dimensional space. This is the same maximal projected-chord
    induction; an orthonormal extension supplies axes after a zero projected
    diameter. Only the eventual sealed frame laws may be used downstream.
    Source context and the exterior norm background: GreedyChordFrameUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric InnerNormalization OrthonormalFamilies
  OrthonormalProjection OrthonormalCapacityExtension LinearBasis FiniteBasisComparison InfiniteSequence
  CompactLinearChordMaximum Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Residual.
Variable R : realType.
Variable n k : nat.
Local Notation V := (R_n R n).
Local Notation B := (@euclidean_inner_product R n).

(** Source for [private_chord_residual]: private finite-sum
    witness for the successive projections in 2.10.38,
    p. 199. Its implementation stays behind the sealed
    frame interface; its laws are proved below. *)
Definition private_chord_residual (e : 'I_k -> V) l (v : V) :=
  v-\sum_(j<k | (j<l)%N) B v (e j)*:e j.

(** Source for [private_chord_residual_linear]: supporting
    linearity of the private projection witness for
    2.10.38, p. 199. *)
Lemma private_chord_residual_linear e l : linear (private_chord_residual e l).
Proof.
move=> a x y; rewrite /private_chord_residual.
have he j : B (a*:x+y) (e j)=a*B x (e j)+B y (e j).
  by rewrite (bilDl (@euclidean_inner_bilinear R n)) (bilZl (@euclidean_inner_bilinear R n)).
under eq_bigr do rewrite he scalerDl -scalerA.
by rewrite big_split scalerBr scaler_sumr opprD addrACA.
Qed.
HB.instance Definition _ e l := GRing.isLinear.Build R V V *:%R
  (private_chord_residual e l) (private_chord_residual_linear e l).

(** Source for [private_chord_residual_full]: supporting
    identification with the perpendicular projection to the
    whole current axis family in 2.10.38, p. 199. *)
Lemma private_chord_residual_full e v :
  private_chord_residual e k v=v-orthonormal_projection (@euclidean_inner_productP R n) e v.
Proof.
rewrite /private_chord_residual /orthonormal_projection.
congr (v-_); apply: eq_big=> j; first exact: ltn_ord.
by move=> _; rewrite inner_coordinateE.
Qed.
End Residual.

(** Source for [private_chord_residual_zero]: private
    starting identity projection for 2.10.38, p. 199. *)
Lemma private_chord_residual_zero (R : realType) n k
    (e : 'I_k -> R_n R n) v : private_chord_residual e 0 v=v.
Proof.
rewrite /private_chord_residual big_pred0; last by move=> j; rewrite ltn0.
exact: subr0.
Qed.

(** Source for [private_chord_residual_successor]: private
    successive perpendicular-projection recursion required by
    the public frame specification for 2.10.38, p. 199. *)
Lemma private_chord_residual_successor (R : realType) n k
    (e : 'I_k -> R_n R n) (i : 'I_k) v :
  private_chord_residual e i.+1 v=private_chord_residual e i v-
    euclidean_inner_product v (e i)*:e i.
Proof.
pose B := @euclidean_inner_product R n.
have hs : (\sum_(j<k | (j<i.+1)%N) B v (e j)*:e j)=
    (\sum_(j<k | (j<i)%N) B v (e j)*:e j)+B v (e i)*:e i.
  rewrite (big_ord_narrow (ltn_ord i)) big_ord_recr
    (big_ord_narrow (ltnW (ltn_ord i))).
  congr (_+_).
  - apply: eq_bigr=> j _; congr (B v _*:_); congr (e _); exact: val_inj.
  - congr (B v _*:_); congr (e _); exact: val_inj.
by rewrite /private_chord_residual hs opprD addrA.
Qed.

(** Source for [private_chord_residual_snoc]: supporting
    preservation of all earlier projected chords on adding
    the next axis in 2.10.38, p. 199. *)
Lemma private_chord_residual_snoc (R : realType) n k
    (e : 'I_k -> R_n R n) u l v : (l<=k)%N ->
  private_chord_residual (ordinal_snoc e u) l v=private_chord_residual e l v.
Proof.
move=> hl; rewrite /private_chord_residual big_mkcond big_ord_recr /=.
have hkl : ~~(k<l)%N by rewrite -leqNgt.
rewrite (negbTE hkl) addr0.
congr (v-_); rewrite -big_mkcond; apply: eq_big=> j // hj.
by rewrite ordinal_snoc_before.
Qed.

(** Source for [private_greedy_chord_prefix]: private
    induction invariant for the first k choices in
    2.10.38, p. 199. The public specification is
    GreedyChordFrameUP.v; this implementation predicate is
    used only to prove its existence. *)
Definition private_greedy_chord_prefix (R : realType) n k
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (e a b : 'I_k -> R_n R n) (c : 'I_k -> R) :=
  orthonormal_family (@euclidean_inner_product R n) e /\
  (forall i, S (a i) /\ S (b i)) /\
  (forall i : 'I_k, private_chord_residual e i (a i-b i)=c i*:e i) /\
  forall (i : 'I_k) x y, S x -> S y ->
    inner_norm (@euclidean_inner_productP R n) (private_chord_residual e i (x-y))<=c i.

(** Source for [private_greedy_chord_prefix_exists]: private
    maximal projected-chord induction proving the existence
    needed for 2.10.38, pp. 198–199. Projected
    diameter zero is handled by an orthonormal extension;
    this permits compact sets in proper affine subspaces. *)
Theorem private_greedy_chord_prefix_exists (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact S -> S !=set0 -> forall k, (k<=n)%N ->
    exists (e a b : 'I_k -> R_n R n) (c : 'I_k -> R),
      private_greedy_chord_prefix S e a b c.
Proof.
move=> hS hne.
elim=> [|k IH] hk.
- exists (fun _=>0),(fun _=>0),(fun _=>0),(fun _=>0).
  split; first by move=> i; have := ltn_ord i; rewrite ltn0.
  split; first by move=> i; have := ltn_ord i; rewrite ltn0.
  split; by move=> i; have := ltn_ord i; rewrite ltn0.
- have [e [a [b [c [he [hab [hsel hmax]]]]]]] := IH (leq_trans (leqnSn k) hk).
  pose P := GRing.Linear.clone _ _ _ _ (private_chord_residual e k) _.
  have [a0 [b0 [ha0 [hb0 hpair]]]] := compact_linear_chord_maximum P hS hne.
  pose d := P (a0-b0).
  have hdorth j : euclidean_inner_product d (e j)=0.
    rewrite /d /P /= private_chord_residual_full.
    exact (@orthonormal_residual_orthogonal R (R_n R n) _ (@euclidean_inner_productP R n)
      (Finite.clone 'I_k _) e he (a0-b0) j).
  have [u [hu [hue hdu]]] : exists u : R_n R n,
      euclidean_inner_product u u= 1 /\
      (forall j, euclidean_inner_product u (e j)=0) /\
      d=inner_norm (@euclidean_inner_productP R n) d*:u.
    case: (eqVneq d 0)=> [hd|hd].
    + have [u [hu hue]] := @orthonormal_capacity_next_vector R (R_n R n)
        _ (@euclidean_inner_productP R n) n (@coordinate_basis R n)
        (finite_basis_independent (@coordinate_basisP R n)) k e he hk.
      exists u; split=> //; split=> //; by rewrite hd inner_norm0 scale0r.
    + exists (inner_normalize (@euclidean_inner_productP R n) d).
      split; first exact: inner_normalize_square hd.
      split; first by move=> j; exact (@inner_normalize_orthogonal R (R_n R n)
        _ (@euclidean_inner_productP R n) d (e j) (hdorth j)).
      symmetry; exact: inner_normalizeK hd.
  exists (ordinal_snoc e u),(ordinal_snoc a a0),(ordinal_snoc b b0),
    (ordinal_snoc c (inner_norm (@euclidean_inner_productP R n) d)).
  split; first exact (@orthonormal_snoc R (R_n R n) _ (@euclidean_inner_productP R n)
    k e u he hu hue).
  split.
  + move=> i; case: (unliftP ord_max i)=> [j ->|->].
    * rewrite !ordinal_snoc_lift; exact: hab.
    * by rewrite !ordinal_snoc_last.
  split.
  + move=> i; case: (unliftP ord_max i)=> [j ->|->].
    * rewrite !ordinal_snoc_lift.
      have hj : (lift ord_max j : nat)=j by rewrite lift_max.
      rewrite hj private_chord_residual_snoc; last exact: ltnW (ltn_ord j).
      exact: hsel.
    * rewrite !ordinal_snoc_last private_chord_residual_snoc; last exact: leqnn.
      exact: hdu.
  + move=> i x y hx hy; case: (unliftP ord_max i)=> [j ->|->].
    * rewrite ordinal_snoc_lift.
      have hj : (lift ord_max j : nat)=j by rewrite lift_max.
      rewrite hj private_chord_residual_snoc; last exact: ltnW (ltn_ord j).
      exact: hmax j x y hx hy.
    * rewrite ordinal_snoc_last private_chord_residual_snoc; last exact: leqnn.
      exact: hpair x y hx hy.
Qed.
