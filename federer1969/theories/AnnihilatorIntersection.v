(** Federer (1969), 1.6.3, p. 25, annihilator of an intersection. We prove
    the annihilator identity directly using the project's linear-extension
    theorem; finite dimension is unnecessary. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors Annihilator SubspaceEquality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Intersection.
Variable K : fieldType.
Variable V : lmodType K.
Variables S T : subspace V.

(** Source for [subspace_intersection]: Federer 1.6.3, p. 25,
    intersection of associated spaces. Supporting abstract definition
    by the conjunction of their membership predicates. *)
Definition subspace_intersection : subspace V.
Proof.
apply: (@Subspace K V (fun v => S v /\ T v)).
- split; exact: subspace_zero.
- move=> x y [hs ht] [hs' ht']; split; exact: subspace_add.
- move=> c x [hs ht]; split; exact: subspace_scale.
Defined.

(** Source for [annihilator_split_graph]: Federer 1.6.3, p. 25,
    annihilator of an intersection. Supporting construction: on S+T,
    assign to x+y the value of a on y, with x in S and y in T. *)
Definition annihilator_split_graph (a : Hom V K^o) v z :=
  exists x y, S x /\ T y /\ v = x+y /\ z = a y.

(** Source for [annihilator_split_graph_linear]: Federer 1.6.3,
    p. 25, annihilator of an intersection. Supporting existence proof:
    the split assignment is a well-defined linear graph precisely under
    the vanishing hypothesis on S intersect T needed here. *)
Lemma annihilator_split_graph_linear a :
  annihilator subspace_intersection a -> linear_graph (annihilator_split_graph a).
Proof.
move=> ha; split.
- exists 0, 0; repeat split; try exact: subspace_zero.
  + by rewrite add0r.
  + by rewrite linear0.
split.
- move=> v w z u [x [y [hs [ht [-> ->]]]]]
    [x' [y' [hs' [ht' [-> ->]]]]].
  exists (x+x'), (y+y'); repeat split.
  + exact: subspace_add hs hs'.
  + exact: subspace_add ht ht'.
  + exact: addrACA.
  + exact: esym (linD (hom_linear a) y y').
split.
- move=> c v z [x [y [hs [ht [-> ->]]]]].
  exists (c *: x), (c *: y); repeat split.
  + exact: subspace_scale hs.
  + exact: subspace_scale ht.
  + exact: scalerDr.
  + exact: esym (linZ (hom_linear a) c y).
- move=> v z u [x [y [hs [ht [hv ->]]]]]
    [x' [y' [hs' [ht' [hv' ->]]]]].
  have hy : y-y' = x'-x.
    apply: (@addIr _ y'); rewrite subrK.
    apply: (@addIr _ x); rewrite addrAC subrK.
    by rewrite [y+x]addrC -hv hv'.
  have hz : a (y-y') = 0.
    apply: ha; split; last exact: subspace_sub ht ht'.
    rewrite hy; exact: subspace_sub hs' hs.
  move: hz; rewrite (linB (hom_linear a)); exact: subr0_eq.
Qed.

(** Source for [annihilator_intersection]: Federer 1.6.3, p. 25, sentence
    preceding the corollary. Direct assertion: annihilating S intersect T is
    equivalent to being a sum of a functional annihilating S and one
    annihilating T. The proof works in arbitrary dimension. *)
Theorem annihilator_intersection a :
  annihilator subspace_intersection a <->
  exists b c : Hom V K^o, annihilator S b /\ annihilator T c /\ a = b+c.
Proof.
split.
- move=> ha.
  pose hg := annihilator_split_graph_linear ha.
  pose b := hom_of_linear (GRing.Linear.clone _ _ _ _ (linear_extension hg) _).
  have hb x y : S x -> T y -> b (x+y) = a y.
    move=> hx hy; apply: linear_extensionE; exists x, y; by repeat split.
  exists b, (a-b); split.
  + move=> x hx; rewrite -[x]addr0 hb //; [exact: linear0 | exact: subspace_zero].
  + split.
    * move=> y hy.
      have hby : b y = a y.
        by rewrite -{1}[y]add0r hb //; exact: subspace_zero.
      change (a y - b y = 0); by rewrite hby subrr.
    * by rewrite addrC subrK.
- move=> [b [c [hb [hc ->]]]] v [hs ht].
  by rewrite hom_addE hb // hc // add0r.
Qed.
End Intersection.

(** Source for [annihilator_separates]: Federer 1.6.3, p. 25,
    annihilator interpretation under duality. Supporting separation
    theorem: the common kernel of all functionals annihilating S is S.
    This proves the double-annihilator principle on the original space
    without assuming finite dimension or identifying it with its bidual. *)
Theorem annihilator_separates (K : fieldType) (V : lmodType K)
  (S : subspace V) v :
  S v <-> forall a : Hom V K^o, annihilator S a -> a v = 0.
Proof.
split; first by move=> hv a ha; exact: ha v hv.
move=> hv.
pose proj := linear_comp (subspace_inclusion S) (subspace_retraction S).
have hzero : v - proj v = 0.
  apply: linear_functionals_separate => f.
  pose a := f - hom_of_linear (linear_comp (hom_as_linear f) proj).
  have ha : annihilator S a.
    move=> x hx; change (f x - f (subspace_inclusion S (subspace_retraction S x)) = 0).
    by rewrite subspace_retraction_on // subrr.
  have hh := hv a ha.
  change (f v - f (proj v) = 0) in hh; by rewrite linearB hh linear0.
have he : v = proj v := subr0_eq hzero.
rewrite he; exact: subspace_valP.
Qed.
