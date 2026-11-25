(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import ExteriorCore.
From Federer Require Import LinearBasis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** The coordinate lemmas exterior_augmentation_word and
    exterior_degree_one_word are proved in ExteriorGrading.v. *)

(** Federer 1.3.2, last paragraph: wedge* R is R direct-sum R, with degrees
    zero and one. Products of two or more vectors in a line vanish. *)
Section ALine.
Variable K : fieldType.
Local Notation L := (GRing.Lmodule.clone K K^o _).
Local Notation E := (exterior_space L).
Local Notation C := (Choice.clone bool _).
Local Notation F := (GRing.Lmodule.clone K (free_vector K C) _).
Local Notation wb := (wedge_bilinear L).

(** Source for [exterior_generator_line]: Federer (1969), 1.3.2, p. 14, last
    paragraph, the exterior algebra of R. In words: The exterior algebra of
    a line has only its scalar and degree-one summands; this is the starting
    point for the ordered-basis argument. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma exterior_generator_line (a : K^o) :
  exterior_generator a = (a : K) *: exterior_generator (1 : K^o).
Proof.
have h : exterior_generator ((a : K) *: (1 : K^o)) =
    (a : K) *: exterior_generator (1 : K^o) by rewrite linearZ.
change (@exterior_generator K L ((a : K) * 1) =
  (a : K) *: @exterior_generator K L (1 : K^o)) in h.
by rewrite mulr1 in h.
Qed.
(** Source for [exterior_word_line_two]: Federer (1969), 1.3.2, p. 14, last
    paragraph, the exterior algebra of R. In words: The exterior algebra of
    a line has only its scalar and degree-one summands; this is the starting
    point for the ordered-basis argument. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma exterior_word_line_two (a b : K^o) (s : seq K^o) :
  exterior_word (a :: b :: s) = (0 : E).
Proof.
rewrite !exterior_word_cons (exterior_generator_line a) (exterior_generator_line b)
  (bilZl wb) (bilZl wb) (bilZr wb) wedge_assoc exterior_generator_square (bil0l wb).
by rewrite !scaler0.
Qed.

(** Source for [exterior_line_reconstruction]: Federer (1969), 1.3.2, p. 14,
    last paragraph, the exterior algebra of R. In words: The exterior
    algebra of a line has only its scalar and degree-one summands; this is
    the starting point for the ordered-basis argument. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma exterior_line_reconstruction (x : E) :
  x = exterior_scalar L (exterior_augmentation L x) +
    exterior_generator (exterior_degree_one L x).
Proof.
elim/exterior_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0 add0r.
- by rewrite !linearD {1}hx {1}hy addrACA.
- by rewrite !linearZ {1}hx scalerDr.
rewrite exterior_augmentation_word exterior_degree_one_word.
case: s => [|a [|b s]]; rewrite /word_degree_zero /word_degree_one /=.
- by rewrite /exterior_scalar scale1r linear0 addr0.
- by rewrite /exterior_scalar scale0r add0r.
- by rewrite exterior_word_line_two /exterior_scalar scale0r linear0 add0r.
Qed.

(** Source for [exterior_line_basis]: Federer (1969), 1.3.2, p. 14, last
    paragraph, the exterior algebra of R. In words: The exterior algebra of
    a line has only its scalar and degree-one summands; this is the starting
    point for the ordered-basis argument. Definition or construction used to
    formalise this passage. *)
Definition exterior_line_basis (b : C) : E :=
  if b then exterior_generator (1 : K^o) else exterior_unit L.
(** Source for [exterior_line_augmentation]: Federer (1969), 1.3.2, p. 14,
    last paragraph, the exterior algebra of R. In words: The exterior
    algebra of a line has only its scalar and degree-one summands; this is
    the starting point for the ordered-basis argument. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma exterior_line_augmentation (c : F) :
  exterior_augmentation L (basis_synthesis exterior_line_basis c) = c false.
Proof.
apply: (free_linear_ext (linear_comp (exterior_augmentation L) (basis_synthesis exterior_line_basis))
  (GRing.Linear.clone _ _ _ _ (@free_eval K C false) _)) c => b.
change (exterior_augmentation L (basis_synthesis exterior_line_basis (delta K b)) = delta K b false).
rewrite basis_synthesisE /exterior_line_basis; case: b; rewrite deltaE /=.
- exact: (exterior_augmentation_word [:: (1 : K^o)]).
- exact: exterior_augmentation_unit.
Qed.
(** Source for [exterior_line_first]: Federer (1969), 1.3.2, p. 14, last
    paragraph, the exterior algebra of R. In words: The exterior algebra of
    a line has only its scalar and degree-one summands; this is the starting
    point for the ordered-basis argument. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma exterior_line_first (c : F) :
  exterior_degree_one L (basis_synthesis exterior_line_basis c) = c true.
Proof.
apply: (free_linear_ext (linear_comp (exterior_degree_one L) (basis_synthesis exterior_line_basis))
  (GRing.Linear.clone _ _ _ _ (@free_eval K C true) _)) c => b.
change (exterior_degree_one L (basis_synthesis exterior_line_basis (delta K b)) = delta K b true).
rewrite basis_synthesisE /exterior_line_basis; case: b; rewrite deltaE /=.
- exact: exterior_generatorK.
- exact: (exterior_degree_one_word (V:=L) [::]).
Qed.

(** Source for [exterior_line_basisP]: Federer (1969), 1.3.2, p. 14, last
    paragraph, the exterior algebra of R. In words: The exterior algebra of
    a line has only its scalar and degree-one summands; this is the starting
    point for the ordered-basis argument. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma exterior_line_basisP : is_basis exterior_line_basis.
Proof.
apply/basisP; split.
- move=> c d heq; apply/fsfunP=> b; case: b.
  - exact: eq_trans (esym (exterior_line_first c))
      (eq_trans (congr1 (exterior_degree_one L) heq) (exterior_line_first d)).
  - exact: eq_trans (esym (exterior_line_augmentation c))
      (eq_trans (congr1 (exterior_augmentation L) heq) (exterior_line_augmentation d)).
- move=> x; exists ((exterior_augmentation L x : K) *: delta K false +
    (exterior_degree_one L x : K) *: delta K true).
  rewrite linearD !linearZ_LR !basis_synthesisE.
  change ((exterior_augmentation L x : K) *: exterior_unit L +
    (exterior_degree_one L x : K) *: exterior_generator (1 : K^o) = x).
  rewrite -exterior_generator_line.
  exact: esym (exterior_line_reconstruction x).
Qed.
(** Source for [exterior_line_graded_basis]: Federer (1969), 1.3.2, p. 14,
    last paragraph, the exterior algebra of R. In words: The exterior
    algebra of a line has only its scalar and degree-one summands; this is
    the starting point for the ordered-basis argument. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma exterior_line_graded_basis : is_graded_basis (exterior_grading L)
  exterior_line_basis (fun b => if b then 1%N else 0%N).
Proof.
split; first exact: exterior_line_basisP.
by case; [exact: exterior_generator_homogeneous | exact: exterior_unit_homogeneous].
Qed.

(** Source for [exterior_line_split]: Federer (1969), 1.3.2, p. 14, last
    paragraph, the exterior algebra of R. In words: The exterior algebra of
    a line has only its scalar and degree-one summands; this is the starting
    point for the ordered-basis argument. Definition or construction used to
    formalise this passage. *)
Definition exterior_line_split (x : E) : (K^o * K^o)%type :=
  (exterior_augmentation L x, exterior_degree_one L x).
(** Source for [exterior_line_split_linear]: Federer (1969), 1.3.2, p. 14,
    last paragraph, the exterior algebra of R. In words: The exterior
    algebra of a line has only its scalar and degree-one summands; this is
    the starting point for the ordered-basis argument. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma exterior_line_split_linear : linear exterior_line_split.
Proof. by move=> a x y; rewrite /exterior_line_split !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K E (K^o * K^o)%type *:%R
  exterior_line_split exterior_line_split_linear.
(** Source for [exterior_line_merge]: Federer (1969), 1.3.2, p. 14, last
    paragraph, the exterior algebra of R. In words: The exterior algebra of
    a line has only its scalar and degree-one summands; this is the starting
    point for the ordered-basis argument. Definition or construction used to
    formalise this passage. *)
Definition exterior_line_merge (p : (K^o * K^o)%type) : E :=
  exterior_scalar L p.1 + exterior_generator p.2.
(** Source for [exterior_line_merge_linear]: Federer (1969), 1.3.2, p. 14,
    last paragraph, the exterior algebra of R. In words: The exterior
    algebra of a line has only its scalar and degree-one summands; this is
    the starting point for the ordered-basis argument. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma exterior_line_merge_linear : linear exterior_line_merge.
Proof.
move=> a [x x'] [y y']; rewrite /exterior_line_merge /= !linearP.
change (a *: exterior_scalar L x + exterior_scalar L y +
  (a *: exterior_generator x' + exterior_generator y') =
  x *: (a *: exterior_unit L) + a *: exterior_generator x' +
  (exterior_scalar L y + exterior_generator y')).
by rewrite /exterior_scalar !scalerA [x * a]mulrC addrACA.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K (K^o * K^o)%type E *:%R
  exterior_line_merge exterior_line_merge_linear.
(** Source for [exterior_line_splitK]: Federer (1969), 1.3.2, p. 14, last
    paragraph, the exterior algebra of R. In words: The exterior algebra of
    a line has only its scalar and degree-one summands; this is the starting
    point for the ordered-basis argument. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma exterior_line_splitK : cancel exterior_line_split exterior_line_merge.
Proof. by move=> x; exact: esym (exterior_line_reconstruction x). Qed.
(** Source for [exterior_line_mergeK]: Federer (1969), 1.3.2, p. 14, last
    paragraph, the exterior algebra of R. In words: The exterior algebra of
    a line has only its scalar and degree-one summands; this is the starting
    point for the ordered-basis argument. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma exterior_line_mergeK : cancel exterior_line_merge exterior_line_split.
Proof.
move=> [a b]; change ((exterior_augmentation L (exterior_scalar L a + exterior_generator b),
  exterior_degree_one L (exterior_scalar L a + exterior_generator b)) = (a,b)).
rewrite !linearD exterior_scalarK exterior_generatorK.
have h0 : exterior_augmentation L (exterior_generator b) = 0.
  exact: (exterior_augmentation_word [:: b]).
have h1 : exterior_degree_one L (exterior_scalar L a) = 0.
  rewrite /exterior_scalar linearZ.
  have hu : exterior_degree_one L (exterior_unit L) = 0.
    exact: (exterior_degree_one_word (V:=L) [::]).
  rewrite hu; change ((a : K) * 0 = 0); exact: mulr0.
by rewrite h0 h1 addr0 add0r.
Qed.
End ALine.

(** Federer 1.3.2, zero-dimensional case of the basis assertion. *)
Section ZeroSpace.
Variable K : fieldType.
Variable V : lmodType K.
Hypothesis hV : forall v : V, v = 0.
Local Notation C := (Choice.clone unit _).
Local Notation E := (exterior_space V).
Local Notation F := (GRing.Lmodule.clone K (free_vector K C) _).

(** Source for [exterior_word_zero_space]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma exterior_word_zero_space (v : V) s : exterior_word (v :: s) = (0 : E).
Proof. by rewrite exterior_word_cons (hV v) linear0 (bil0l (wedge_bilinear V)). Qed.
(** Source for [exterior_zero_reconstruction]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma exterior_zero_reconstruction (x : E) : x = exterior_scalar V (exterior_augmentation V x).
Proof.
elim/exterior_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD {1}hx {1}hy.
- by rewrite !linearZ {1}hx.
rewrite exterior_augmentation_word; case: s => [|v s]; rewrite /word_degree_zero /= /exterior_scalar.
- by rewrite scale1r.
- by rewrite exterior_word_zero_space scale0r.
Qed.
(** Source for [exterior_zero_basis]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition exterior_zero_basis (_ : C) : E := exterior_unit V.
(** Source for [exterior_zero_coordinate]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma exterior_zero_coordinate (c : F) :
  exterior_augmentation V (basis_synthesis exterior_zero_basis c) = c tt.
Proof.
apply: (free_linear_ext (linear_comp (exterior_augmentation V) (basis_synthesis exterior_zero_basis))
  (GRing.Linear.clone _ _ _ _ (@free_eval K C tt) _)) c => [[]].
change (exterior_augmentation V (basis_synthesis exterior_zero_basis (delta K tt)) = delta K tt tt).
by rewrite basis_synthesisE exterior_augmentation_unit deltaE.
Qed.
(** Source for [exterior_zero_basisP]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma exterior_zero_basisP : is_basis exterior_zero_basis.
Proof.
apply/basisP; split.
- move=> c d heq; apply/fsfunP=> [[]].
  exact: eq_trans (esym (exterior_zero_coordinate c))
    (eq_trans (congr1 (exterior_augmentation V) heq) (exterior_zero_coordinate d)).
- move=> x; exists ((exterior_augmentation V x : K) *: delta K tt).
  rewrite linearZ basis_synthesisE.
  exact: esym (exterior_zero_reconstruction x).
Qed.
(** Source for [exterior_zero_graded_basis]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma exterior_zero_graded_basis : is_graded_basis (exterior_grading V)
  exterior_zero_basis (fun _ => 0%N).
Proof. split; first exact: exterior_zero_basisP. by move=> []; exact: exterior_unit_homogeneous. Qed.
End ZeroSpace.
