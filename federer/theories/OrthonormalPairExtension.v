(** Federer (1969), 1.7.3, pp. 29-30: combining the orthonormal pairs of
    mutually perpendicular invariant pieces. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthonormalFamilies
  SkewNormalFormUP InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [orthonormal_pair_extension]: Federer 1.7.3,
    pp. 29-30, append an orthonormal pair perpendicular to
    every earlier pair, preserving orthonormality of the whole sequence. *)
Lemma orthonormal_pair_extension (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) m (a b : 'I_m -> V)
    (ho : orthonormal_family B (paired_family a b)) x y
    (hx : B x x = 1) (hy : B y y = 1) (hxy : B x y = 0)
    (hox : forall p, B (paired_family a b p) x = 0)
    (hoy : forall p, B (paired_family a b p) y = 0) :
  orthonormal_family B
    (paired_family (ordinal_snoc a x) (ordinal_snoc b y)).
Proof.
move=> [i bi] [j bj].
case: (unliftP ord_max i) => [u ->|->];
  case: (unliftP ord_max j) => [v ->|->].
- rewrite /paired_family /= !ordinal_snoc_lift.
  have hh := ho (u,bi) (v,bj).
  rewrite !xpair_eqE (inj_eq (@lift_inj m.+1 (ord_max : 'I_m.+1))).
  exact hh.
- have hi : lift ord_max u != (ord_max : 'I_m.+1).
    apply/eqP=> hh; have hv := congr1 val hh.
    change ((lift ord_max u : nat) = m) in hv.
    rewrite lift_max in hv; by move: (ltn_ord u); rewrite hv ltnn.
  rewrite xpair_eqE (negbTE hi) /= /paired_family /= !ordinal_snoc_lift !ordinal_snoc_last.
  case: bi; case: bj;
    first [exact (hoy (u,true)) | exact (hox (u,true)) |
      exact (hoy (u,false)) | exact (hox (u,false))].
- have hi : (ord_max : 'I_m.+1) != lift ord_max v.
    apply/eqP=> hh; have hv := congr1 val hh.
    change (m = (lift ord_max v : nat)) in hv.
    rewrite lift_max in hv; by move: (ltn_ord v); rewrite -hv ltnn.
  rewrite xpair_eqE (negbTE hi) /= /paired_family /= !ordinal_snoc_lift !ordinal_snoc_last.
  rewrite (inner_symmetric hB).
  case: bi; case: bj; [exact: hoy (v,true) | exact: hoy (v,false) |
    exact: hox (v,true) | exact: hox (v,false)].
- rewrite xpair_eqE eqxx /= /paired_family /= !ordinal_snoc_last.
  case: bi; case: bj => /=; rewrite ?hx ?hy ?hxy //.
  by rewrite (inner_symmetric hB) hxy.
Qed.
