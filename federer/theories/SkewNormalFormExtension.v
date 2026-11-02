(** Federer (1969), 1.7.3, pp. 29-30: assembling the normal form from
    mutually perpendicular invariant pieces. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient InnerProductUP Bilinear
  OrthogonalComplement SkewPairUP SkewPairCoordinates SkewNormalFormUP
  OrthonormalPairExtension InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Extension.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable f : {linear V -> V}.
Variables W Q Z : subspace V.
Hypothesis hQW : forall x, Q x -> W x.
Hypothesis hZW : forall x, Z x -> W x.
Hypothesis hQZ : forall x, Q x -> orthogonal_complement hB Z x.
Hypothesis hsplit : forall x, W x -> exists z q, Z z /\ Q q /\ x = z+q.
Variable m : nat.
Variables a b : 'I_m -> V.
Variable lambda : 'I_m -> R.
Hypothesis hN : is_skew_normal_form_on B f Q a b lambda.

(** Source for [skew_pair_drop_orthogonal_left]: Federer
    1.7.3, pp. 29-30, supporting coordinate identity: a vector
    in Z contributes zero to coordinates along a pair in Q. *)
Lemma skew_pair_drop_orthogonal_left u v z q y :
  Q u -> Q v -> Z z ->
  skew_pair_form B u v (z+q) y = skew_pair_form B u v q y.
Proof.
move=> hu hv hz.
have hzu : B z u = 0 by rewrite (inner_symmetric hB); exact (@hQZ u hu z hz).
have hzv : B z v = 0 by rewrite (inner_symmetric hB); exact (@hQZ v hv z hz).
by rewrite /skew_pair_form !(bilDl (inner_bilinear hB)) hzu hzv !add0r.
Qed.

(** Source for [skew_pair_drop_orthogonal_right]: Federer
    1.7.3, pp. 29-30, supporting coordinate identity: a vector
    in Q contributes zero to coordinates along a pair in Z. *)
Lemma skew_pair_drop_orthogonal_right u v z q y :
  Z u -> Z v -> Q q ->
  skew_pair_form B u v (z+q) y = skew_pair_form B u v z y.
Proof.
move=> hu hv hq.
by rewrite /skew_pair_form !(bilDl (inner_bilinear hB))
  (@hQZ q hq u hu) (@hQZ q hq v hv) !addr0.
Qed.

(** Source for [skew_normal_extend_zero]: Federer 1.7.3,
    pp. 29-30, a zero invariant piece contributes no pair
    or coefficient to the two-form normal form. *)
Theorem skew_normal_extend_zero (hzero : forall z, Z z -> f z = 0) :
  is_skew_normal_form_on B f W a b lambda.
Proof.
constructor.
- move=> i; apply: hQW; exact: (skew_normal_first_in hN).
- move=> i; apply: hQW; exact: (skew_normal_second_in hN).
- exact: skew_normal_orthonormal hN.
- exact: skew_normal_nonnegative hN.
- move=> x hx y; have [z [q [hz [hq he]]]] := @hsplit x hx.
  rewrite he linearD (@hzero z hz) add0r
    (@skew_normal_equation R V B f Q m a b lambda hN q hq y).
  apply: eq_bigr => i _; congr (lambda i * _); symmetry.
  apply: (@skew_pair_drop_orthogonal_left (a i) (b i) z q y _ _ hz).
  + exact (@skew_normal_first_in R V B f Q m a b lambda hN _).
  + exact (@skew_normal_second_in R V B f Q m a b lambda hN _).
Qed.

(** Source for [skew_normal_extend_pair]: Federer 1.7.3,
    pp. 29-30, a two-dimensional invariant piece adds one
    orthonormal pair and its nonnegative coefficient to the normal form. *)
Theorem skew_normal_extend_pair u v r
    (hu : Z u) (hv : Z v) (hp : is_skew_pair B f u v r)
    (hspan : forall z, Z z -> exists c d : R, z = c *: u+d *: v) :
  is_skew_normal_form_on B f W
    (ordinal_snoc a u) (ordinal_snoc b v) (ordinal_snoc lambda r).
Proof.
constructor.
- move=> i; case: (unliftP ord_max i) => [j ->|->];
    rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + apply: hQW; exact (@skew_normal_first_in R V B f Q m a b lambda hN _).
  + exact: hZW hu.
- move=> i; case: (unliftP ord_max i) => [j ->|->];
    rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + apply: hQW; exact (@skew_normal_second_in R V B f Q m a b lambda hN _).
  + exact: hZW hv.
- apply: (@orthonormal_pair_extension R V B hB m a b
    (skew_normal_orthonormal hN) u v (skew_pair_first_unit hp)
    (skew_pair_second_unit hp) (skew_pair_orthogonal hp)).
  + move=> [i bi]; apply: (@hQZ _ _ u hu).
    case: bi; [exact (@skew_normal_second_in R V B f Q m a b lambda hN _) | exact (@skew_normal_first_in R V B f Q m a b lambda hN _)].
  + move=> [i bi]; apply: (@hQZ _ _ v hv).
    case: bi; [exact (@skew_normal_second_in R V B f Q m a b lambda hN _) | exact (@skew_normal_first_in R V B f Q m a b lambda hN _)].
- move=> i; case: (unliftP ord_max i) => [j ->|->];
    rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact (@skew_normal_nonnegative R V B f Q m a b lambda hN j).
  + exact: skew_pair_nonnegative hp.
- move=> x hx y; have [z [q [hz [hq he]]]] := @hsplit x hx.
  have hold i : skew_pair_form B (a i) (b i) x y = skew_pair_form B (a i) (b i) q y.
    rewrite he; apply: (@skew_pair_drop_orthogonal_left (a i) (b i) z q y _ _ hz).
    + exact (@skew_normal_first_in R V B f Q m a b lambda hN _).
    + exact (@skew_normal_second_in R V B f Q m a b lambda hN _).
  have hnew : skew_pair_form B u v x y = skew_pair_form B u v z y.
    rewrite he; exact (@skew_pair_drop_orthogonal_right u v z q y hu hv hq).
  have hs : (\sum_i ordinal_snoc lambda r i *
      skew_pair_form B (ordinal_snoc a u i) (ordinal_snoc b v i) x y) =
      (\sum_i lambda i * skew_pair_form B (a i) (b i) q y) +
        r * skew_pair_form B u v z y.
    rewrite big_ord_recr !ordinal_snoc_last hnew.
    congr (_ + _); apply: eq_bigr => i _.
    by rewrite !ordinal_snoc_before hold.
  rewrite hs {1}he linearD (bilDl (inner_bilinear hB)).
  rewrite (@skew_pair_evaluation R V B hB f u v r hp z y (@hspan z hz))
    (@skew_normal_equation R V B f Q m a b lambda hN q hq y).
  exact: addrC.
Qed.
End Extension.
