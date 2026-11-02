(** Federer (1969), 3.1.11, p. 219:
    grouping the first p and last q arguments
    of a continuous (p+q)-linear map. The
    corrected operator norm is unchanged by grouping. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom RealNormUP TensorFamilyUP FamilyUpdate
  ContinuousMultilinearUP MultilinearArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section BlockCurrying.
Variable R : realType.
Variables p q : nat.
Variables X Y Z : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Variable evaluation : {ffun 'I_p->X}->Hom Z Y.
Variable ZN : Z->R.
Hypothesis hZ : is_continuous_multilinear_space NX NY evaluation ZN.

(** Source for [continuous_multilinear_block_curry_exists]:
    a continuous (p+q)-linear map is a
    continuous q-linear map into the p-linear
    space, supporting the D^q D^p identity
    in Federer 3.1.11, p. 219.
    Either block of arguments may be empty. *)
Theorem continuous_multilinear_block_curry_exists
    (f : {ffun 'I_(p+q)->X}->Y) :
  norm_bounded_multilinear NX NY f ->
  exists g : {ffun 'I_q->X}->Z,
    norm_bounded_multilinear NX ZN g /\
    forall u v, evaluation u (g v)=f (multilinear_arguments_join u v).
Proof.
move=> [hf [C [hC hb]]].
have hprod n (v : {ffun 'I_n->X}) : 0<=\prod_(i<n) NX (v i).
  apply: prodr_ge0=>i _; exact (real_seminorm_nonnegative hNX.1 (v i)).
have hfv v : norm_bounded_multilinear NX NY
    (fun u=>f (multilinear_arguments_join u v)).
  split; first exact: multilinear_arguments_fixed_right hf v.
  exists (C*\prod_(i<q) NX (v i)); split; first exact: mulr_ge0 hC (hprod _ _).
  move=> u; have hh := hb (multilinear_arguments_join u v).
  rewrite multilinear_arguments_product in hh.
  have hid : C*((\prod_(i<p) NX (u i))*(\prod_(i<q) NX (v i)))=
    (C*(\prod_(i<q) NX (v i)))*(\prod_(i<p) NX (u i)) by ring.
  by rewrite hid in hh.
have hex v := continuous_multilinear_surjective hZ (hfv v).
have [g hg] := choice hex.
exists g; split; last exact (fun u v=>hg v u).
split.
- move=> v i c x y; apply: (continuous_multilinear_extensional hZ)=>u.
  rewrite linearP /= !hg.
  have hlin := multilinear_arguments_fixed_left hf u.
  exact (@hlin v i c x y).
- exists C; split=> // v.
  apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ (g v))).
  + exact: mulr_ge0 hC (hprod _ _).
  + move=> u; rewrite hg.
    have hh := hb (multilinear_arguments_join u v).
    rewrite multilinear_arguments_product in hh.
    have hid : C*((\prod_(i<p) NX (u i))*(\prod_(i<q) NX (v i)))=
      (C*(\prod_(i<q) NX (v i)))*(\prod_(i<p) NX (u i)) by ring.
    by rewrite hid in hh.
Qed.

(** Source for [continuous_multilinear_block_uncurry]:
    evaluation of a q-linear map with values
    in the abstract p-linear space recovers a
    continuous (p+q)-linear map, supporting
    Federer 3.1.11, p. 219. *)
Theorem continuous_multilinear_block_uncurry
    (g : {ffun 'I_q->X}->Z) :
  norm_bounded_multilinear NX ZN g ->
  norm_bounded_multilinear NX NY
    (fun w=>evaluation (multilinear_arguments_left w)
      (g (multilinear_arguments_right w))).
Proof.
move=> [hg [C [hC hb]]].
pose f (w : {ffun 'I_(p+q)->X}) :=
  evaluation (multilinear_arguments_left w) (g (multilinear_arguments_right w)).
have he u v : f (multilinear_arguments_join u v)=evaluation u (g v).
  by rewrite /f multilinear_arguments_left_join multilinear_arguments_right_join.
change (norm_bounded_multilinear NX NY f).
split.
- move=> w i c x y.
  rewrite -[w](multilinear_arguments_join_split w).
  case: (split_ordP i)=>j ->.
  + rewrite -!multilinear_arguments_join_with_left !he.
    exact: continuous_multilinear_evaluation hZ _ _ j c x y.
  + rewrite -!multilinear_arguments_join_with_right !he hg.
    by rewrite linearP.
- exists C; split=> // w.
  rewrite -[w](multilinear_arguments_join_split w) he multilinear_arguments_product.
  pose u := multilinear_arguments_left w.
  pose v := multilinear_arguments_right w.
  have hh := multilinear_operator_bound (continuous_multilinear_norm_laws hZ (g v)) u.
  have hp : 0<=\prod_(i<p) NX (u i).
    apply: prodr_ge0=>i _; exact (real_seminorm_nonnegative hNX.1 (u i)).
  apply: le_trans hh _.
  have hscale := ler_wpM2r hp (hb v).
  have hid : (C*(\prod_(i<q) NX (v i)))*(\prod_(i<p) NX (u i))=
    C*((\prod_(i<p) NX (u i))*(\prod_(i<q) NX (v i))) by ring.
  by rewrite hid in hscale.
Qed.

(** Source for [continuous_multilinear_block_curry_norm]:
    grouping preserves the operator norm of
    Federer 3.1.11, p. 219, corrected
    by erratum p. 4, book line 4.
    The proof uses least homogeneous bounds, without
    assuming the supremum is attained. *)
Theorem continuous_multilinear_block_curry_norm
    (f : {ffun 'I_(p+q)->X}->Y) (g : {ffun 'I_q->X}->Z) c :
  is_multilinear_operator_norm NX NY f c ->
  (forall u v, evaluation u (g v)=f (multilinear_arguments_join u v)) ->
  is_multilinear_operator_norm NX ZN g c.
Proof.
move=> hf he.
have hprod n (v : {ffun 'I_n->X}) : 0<=\prod_(i<n) NX (v i).
  apply: prodr_ge0=>i _; exact (real_seminorm_nonnegative hNX.1 (v i)).
constructor.
- exact: multilinear_operator_nonnegative hf.
- move=> v; apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ (g v))).
  + exact: mulr_ge0 (multilinear_operator_nonnegative hf) (hprod _ _).
  + move=> u; rewrite he.
    have hh := multilinear_operator_bound hf (multilinear_arguments_join u v).
    rewrite multilinear_arguments_product in hh.
    have hid : c*((\prod_(i<p) NX (u i))*(\prod_(i<q) NX (v i)))=
      (c*(\prod_(i<q) NX (v i)))*(\prod_(i<p) NX (u i)) by ring.
    by rewrite hid in hh.
- move=> C hC hb; apply: (multilinear_operator_least hf hC)=>w.
  rewrite -[w](multilinear_arguments_join_split w) -he multilinear_arguments_product.
  pose u := multilinear_arguments_left w.
  pose v := multilinear_arguments_right w.
  have hh := multilinear_operator_bound (continuous_multilinear_norm_laws hZ (g v)) u.
  apply: le_trans hh _.
  have hs := ler_wpM2r (hprod _ u) (hb v).
  have hid : (C*(\prod_(i<q) NX (v i)))*(\prod_(i<p) NX (u i))=
    C*((\prod_(i<p) NX (u i))*(\prod_(i<q) NX (v i))) by ring.
  by rewrite hid in hs.
Qed.
End BlockCurrying.
