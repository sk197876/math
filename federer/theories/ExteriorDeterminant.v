(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import ExteriorBases.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.4, first paragraph: the top exterior power is a line.
    The determinant is defined by its action on this line, before any
    coefficient formula is considered. *)
(** Source for [Lambda_top_sorted]: Federer (1969), 1.3.4, p. 16, opening
    definition via the top exterior power. In words: An endomorphism acts on
    the one-dimensional top exterior power by multiplication by a unique
    scalar, its determinant. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Lambda_top_sorted n : sorted ltn (map val (ord_tuple n)).
Proof. by rewrite val_ord_tuple val_enum_ord; exact: iota_ltn_sorted. Qed.
(** Source for [Lambda_top]: Federer (1969), 1.3.4, p. 16, opening
    definition via the top exterior power. In words: An endomorphism acts on
    the one-dimensional top exterior power by multiplication by a unique
    scalar, its determinant. Definition or construction used to formalise
    this passage. *)
Definition Lambda_top n : Lambda n n := Sub (ord_tuple n) (Lambda_top_sorted n).
(** Source for [Lambda_top_unique]: Federer (1969), 1.3.4, p. 16, opening
    definition via the top exterior power. In words: An endomorphism acts on
    the one-dimensional top exterior power by multiplication by a unique
    scalar, its determinant. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Lemma Lambda_top_unique n (t : Lambda n n) : t = Lambda_top n.
Proof.
have hc : (#|{:Lambda n n}| <= 1)%N by rewrite card_Lambda binn.
exact: (fintype_le1P hc (Lambda_top n) t).
Qed.

(** Source for [induced_exterior_ext]: Federer (1969), 1.3.4, p. 16, opening
    definition via the top exterior power. In words: An endomorphism acts on
    the one-dimensional top exterior power by multiplication by a unique
    scalar, its determinant. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma induced_exterior_ext (K : fieldType) (V W : lmodType K)
    (f g : {linear V -> W}) : f =1 g -> exterior_algebra_map f =1 exterior_algebra_map g.
Proof.
move=> hfg x; apply: (exterior_algebra_ext (@exterior_algebra_exists K V)
  (exterior_algebra_map f) (exterior_algebra_map g)) x => v.
change (exterior_algebra_map f (exterior_generator v) =
  exterior_algebra_map g (exterior_generator v)).
apply: eq_trans (@exterior_algebra_mapE K V W f v) _.
apply: eq_trans (congr1 (@exterior_generator K W) (hfg v)) _.
exact (esym (@exterior_algebra_mapE K V W g v)).
Qed.

Section TopPower.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variable n : nat.
Variable V : lmodType K.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation L := (exterior_power V n).
Local Notation hb := (finite_e_lambda_basis he h2 n).
(** Source for [top_vector]: Federer (1969), 1.3.4, p. 16, opening
    definition via the top exterior power. In words: An endomorphism acts on
    the one-dimensional top exterior power by multiplication by a unique
    scalar, its determinant. Definition or construction used to formalise
    this passage. *)
Definition top_vector : L := finite_e_lambda e (Lambda_top n).
(** Source for [top_coordinate]: Federer (1969), 1.3.4, p. 16, opening
    definition via the top exterior power. In words: An endomorphism acts on
    the one-dimensional top exterior power by multiplication by a unique
    scalar, its determinant. Definition or construction used to formalise
    this passage. *)
Definition top_coordinate : {linear L -> K^o} :=
  linear_comp (GRing.Linear.clone _ _ _ _ (free_eval (Lambda_top n)) _)
    (basis_coordinates hb).

(** Source for [top_coordinateE]: Federer (1969), 1.3.4, p. 16, opening
    definition via the top exterior power. In words: An endomorphism acts on
    the one-dimensional top exterior power by multiplication by a unique
    scalar, its determinant. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma top_coordinateE : top_coordinate top_vector = 1.
Proof.
change (basis_coordinates hb (finite_e_lambda e (Lambda_top n)) (Lambda_top n) = 1).
by rewrite basis_coordinatesE deltaE eqxx.
Qed.

(** Source for [top_expansion]: Federer (1969), 1.3.4, p. 16, opening
    definition via the top exterior power. In words: An endomorphism acts on
    the one-dimensional top exterior power by multiplication by a unique
    scalar, its determinant. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Lemma top_expansion (x : L) : x = (top_coordinate x : K) *: top_vector.
Proof.
elim/(basis_induction hb): x => [|x y hx hy|a x hx|t].
- by rewrite linear0 scale0r.
- by rewrite linearD scalerDl -hx -hy.
- by rewrite linearZ -scalerA -hx.
- rewrite (Lambda_top_unique t); change (top_vector = (top_coordinate top_vector : K) *: top_vector).
  by rewrite top_coordinateE scale1r.
Qed.

(** Source for [top_scalar_injective]: Federer (1969), 1.3.4, p. 16, opening
    definition via the top exterior power. In words: An endomorphism acts on
    the one-dimensional top exterior power by multiplication by a unique
    scalar, its determinant. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Lemma top_scalar_injective : injective (fun a : K => a *: top_vector).
Proof.
move=> a b h; have hc := congr1 top_coordinate h.
rewrite !linearZ top_coordinateE in hc.
change (a * 1 = b * 1) in hc; by rewrite !mulr1 in hc.
Qed.
(** Source for [top_vector_nonzero]: Federer (1969), 1.3.4, p. 16, opening
    definition via the top exterior power. In words: An endomorphism acts on
    the one-dimensional top exterior power by multiplication by a unique
    scalar, its determinant. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma top_vector_nonzero : top_vector != 0.
Proof.
apply/eqP=> h; have /eqP hc := congr1 top_coordinate h.
by rewrite top_coordinateE linear0 oner_eq0 in hc.
Qed.

(** Source for [det]: Federer (1969), 1.3.4, p. 16, opening definition via
    the top exterior power. In words: An endomorphism acts on the
    one-dimensional top exterior power by multiplication by a unique scalar,
    its determinant. Definition or construction used to formalise this
    passage. *)
Definition det (f : {linear V -> V}) : K :=
  top_coordinate (exterior_power_map f n top_vector).

(** Source for [det_ext]: Federer (1969), 1.3.4, p. 16, opening definition
    via the top exterior power. In words: An endomorphism acts on the
    one-dimensional top exterior power by multiplication by a unique scalar,
    its determinant. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma det_ext (f g : {linear V -> V}) : f =1 g -> det f = det g.
Proof.
move=> hfg; rewrite /det; congr 1 (top_coordinate _); apply: val_inj.
exact (@induced_exterior_ext K V V f g hfg (component_val top_vector)).
Qed.

(** Source for [detE]: Federer (1969), 1.3.4, p. 16, opening definition via
    the top exterior power. In words: An endomorphism acts on the
    one-dimensional top exterior power by multiplication by a unique scalar,
    its determinant. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem detE (f : {linear V -> V}) (x : L) : exterior_power_map f n x = det f *: x.
Proof.
have hx := top_expansion x.
have hf : exterior_power_map f n top_vector = det f *: top_vector.
  exact: top_expansion.
apply: eq_trans (congr1 (exterior_power_map f n) hx) _.
rewrite linearZ hf.
apply: eq_trans _ (esym (congr1 ( *:%R (det f)) hx)).
change ((top_coordinate x : K) *: (det f *: top_vector) =
  det f *: ((top_coordinate x : K) *: top_vector)).
by rewrite !scalerA mulrC.
Qed.

(** Source for [det_unique]: Federer (1969), 1.3.4, p. 16, opening
    definition via the top exterior power. In words: An endomorphism acts on
    the one-dimensional top exterior power by multiplication by a unique
    scalar, its determinant. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem det_unique (f : {linear V -> V}) a :
  (forall x : L, exterior_power_map f n x = a *: x) -> a = det f.
Proof.
move=> h; apply: top_scalar_injective.
by rewrite -(h top_vector) detE.
Qed.

(** Source for [det_exists_unique]: Federer (1969), 1.3.4, p. 16, opening
    definition via the top exterior power. In words: An endomorphism acts on
    the one-dimensional top exterior power by multiplication by a unique
    scalar, its determinant. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem det_exists_unique (f : {linear V -> V}) :
  exists! a : K, forall x : L, exterior_power_map f n x = a *: x.
Proof.
exists (det f); split; first exact: detE.
move=> a ha; symmetry; exact: det_unique ha.
Qed.

(** Source for [top_dimension]: Federer (1969), 1.3.4, p. 16, opening
    definition via the top exterior power. In words: An endomorphism acts on
    the one-dimensional top exterior power by multiplication by a unique
    scalar, its determinant. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Lemma top_dimension : dim (finite_exterior_power h2 he n) = 1%N.
Proof. by rewrite exterior_power_dimension binn. Qed.

(** Federer 1.3.4, composition paragraph: the induced maps compose,
    hence the scalars by which they act on the top power multiply. *)
(** Source for [det_comp]: Federer (1969), 1.3.4, p. 16, paragraph beginning
    If g is another endomorphism. In words: Exterior powers preserve
    composition, so the determinant of a composition is the product of the
    determinants. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem det_comp (f g : {linear V -> V}) : det (linear_comp g f) = det g * det f.
Proof.
symmetry; apply: det_unique => x.
have hc : exterior_power_map (linear_comp g f) n x =
    exterior_power_map g n (exterior_power_map f n x).
  apply: val_inj.
  exact (esym (@exterior_algebra_map_comp K V V V f g (component_val x))).
by rewrite hc !detE scalerA.
Qed.

(** Source for [det_id]: Federer (1969), 1.3.4, p. 16, paragraph beginning
    If g is another endomorphism. In words: Exterior powers preserve
    composition, so the determinant of a composition is the product of the
    determinants. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma det_id : det (linear_id V) = 1.
Proof.
symmetry; apply: det_unique => x; rewrite scale1r; apply: val_inj.
exact (@exterior_algebra_map_id K V (component_val x)).
Qed.
End TopPower.

(** Federer 1.3.4: the scalar is intrinsic, so changing the chosen basis
    does not change det. This also covers the zero-dimensional space. *)
(** Source for [det_basis_independent]: Federer (1969), 1.3.4, p. 16,
    opening definition via the top exterior power. In words: An endomorphism
    acts on the one-dimensional top exterior power by multiplication by a
    unique scalar, its determinant. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem det_basis_independent (K : fieldType) (h2 : (1 + 1 : K) != 0)
    n (V : lmodType K) (e d : 'I_n -> V) (he : is_basis e) (hd : is_basis d)
    (f : {linear V -> V}) :
  det h2 he f = det h2 hd f.
Proof.
apply: (@det_unique K h2 n V d hd f).
exact: (@detE K h2 n V e he f).
Qed.
