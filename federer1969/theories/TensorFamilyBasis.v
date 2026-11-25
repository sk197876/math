(** Federer 1.1.2, p. 10, final paragraph: arbitrary bases of all finite
    factors give a basis of the tensor product. Index sets need not be
    finite or inhabited; all arguments use the public universal property. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp finmap.
From Federer Require Import TensorUP TensorFamily TensorFamilyLift Bilinear
  FreeVector LinearBasis FiniteDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Basis.
Variable K : fieldType.
Variable n : nat.
Variable V : 'I_n -> lmodType K.
Variable J : 'I_n -> choiceType.
Variable e : forall i, J i -> V i.
Arguments e i _ : clear implicits.
Hypothesis he : forall i, is_basis (e i).
Variable T : lmodType K.
Variable mu : {dffun forall i, V i} -> T.
Hypothesis hmu : is_tensor_product_family mu.
Local Notation B := {dffun forall i, J i}.

(** Source for [tensor_basis_arguments]: Federer 1.1.2, p. 10;
    a tuple consisting of one basis vector from each factor. *)
Definition tensor_basis_arguments (b : B) : {dffun forall i, V i} :=
  [ffun i => e i (b i)].

(** Source for [tensor_family_basis]: Federer 1.1.2, p. 10;
    the family of all pure products of the supplied basis vectors. *)
Definition tensor_family_basis (b : B) : T := mu (tensor_basis_arguments b).

(** Source for [multilinear_basis_induction]: Federer 1.1.2, p. 10,
    supporting expansion argument. Closure under linear combinations and
    validity on basis tuples imply validity on every multilinear value. *)
Lemma multilinear_basis_induction (Z : lmodType K)
    (f : {dffun forall i, V i} -> Z) (hf : multilinear f)
    (P : Z -> Prop) :
  P 0 -> (forall x y, P x -> P y -> P (x+y)) ->
  (forall a x, P x -> P (a *: x)) ->
  (forall b, P (f (tensor_basis_arguments b))) -> forall x, P (f x).
Proof.
move=> h0 hD hZ hb.
have step : forall (s : seq 'I_n) (x : {dffun forall i, V i}),
    (forall i, i \notin s -> exists j, x i = e i j) -> P (f x).
  elim=> [|i s hs] x hout.
  - have hex i : exists j, x i = e i j by apply: hout; rewrite in_nil.
    pose b : B := [ffun i => proj1_sig (cid (hex i))].
    have hx : x = tensor_basis_arguments b.
      apply/ffunP=> i; rewrite /tensor_basis_arguments /b !ffunE.
      exact: (proj2_sig (cid (hex i))).
    by rewrite hx; exact: hb.
  - have hv : forall v : V i, P (f (family_with x v)).
      apply: (basis_induction (he i)).
      + by rewrite (lin0 (hf x i)).
      + move=> v w hv hw; rewrite (linD (hf x i)); exact: hD.
      + move=> a v hv; rewrite (linZ (hf x i)); exact: hZ.
      + move=> j; apply: hs=> k hk.
        case: (eqVneq i k)=> [<-|hik].
        * by exists j; rewrite family_with_in.
        * rewrite family_with_out //; apply: hout.
          by rewrite in_cons eq_sym (negPf hik) (negbTE hk).
    by have := hv (x i); rewrite family_with_id.
move=> x; apply: (step (enum 'I_n) x)=> i hi.
by move: hi; rewrite mem_enum.
Qed.

(** Source for [tensor_basis_coefficient_product]: Federer 1.1.2, p. 10;
    product of coordinate functionals detecting a prescribed basis tuple. *)
Definition tensor_basis_coefficient_product (b : B)
    (x : {dffun forall i, V i}) : K^o :=
  \prod_i (basis_coordinates (he i) (x i)) (b i).

(** Source for [tensor_basis_coefficient_multilinear]: Federer 1.1.2,
    p. 10; the detecting product is multilinear. Supporting independence
    argument, requiring no finite-dimensional factor hypothesis. *)
Lemma tensor_basis_coefficient_multilinear b :
  multilinear (tensor_basis_coefficient_product b).
Proof.
move=> x j a v w.
have outside (z : V j) :
  (\prod_(i | i != j) basis_coordinates (he i) (family_with x z i) (b i)) =
  (\prod_(i | i != j) basis_coordinates (he i) (x i) (b i)).
  apply: eq_bigr=> i hi; rewrite family_with_out; first reflexivity.
  by rewrite eq_sym.
have separate y : tensor_basis_coefficient_product b y =
    basis_coordinates (he j) (y j) (b j) *
    (\prod_(i | i != j) basis_coordinates (he i) (y i) (b i)).
  by rewrite /tensor_basis_coefficient_product (bigD1 j).
rewrite !separate !family_with_in !outside linearP free_addE free_scaleE /=.
pose cv := basis_coordinates (he j) v (b j).
pose cw := basis_coordinates (he j) w (b j).
pose rest := \prod_(i | i != j) basis_coordinates (he i) (x i) (b i).
change ((a*cv+cw)*rest = a*(cv*rest)+cw*rest).
by rewrite mulrDl mulrA.
Qed.

(** Source for [tensor_basis_delta_product]: Federer 1.1.2, p. 10;
    evaluation on a basis tuple is its Kronecker coefficient. *)
Lemma tensor_basis_delta_product (b c : B) :
  tensor_basis_coefficient_product b (tensor_basis_arguments c) =
    if b == c then 1 else 0.
Proof.
rewrite /tensor_basis_coefficient_product.
under eq_bigr do rewrite /tensor_basis_arguments ffunE basis_coordinatesE deltaE.
have h s : (\prod_(i <- s) (if b i == c i then (1 : K) else 0)) =
    if all (fun i => b i == c i) s then 1 else 0.
  elim: s=> [|i s hs]; first by rewrite big_nil.
  rewrite big_cons hs /=; by case: (b i == c i); case: (all _ s); rewrite ?mul1r ?mul0r.
have hd : all (fun i => b i == c i) (index_enum 'I_n) = (b == c).
  apply/idP/idP.
  - move/allP=> hcoords; apply/eqP/ffunP=> i; apply/eqP.
    apply: hcoords; exact: mem_index_enum.
  - move/eqP=> ->; apply/allP=> i _; exact: eqxx.
by rewrite h hd.
Qed.

(** Source for [tensor_basis_coordinate]: Federer 1.1.2, p. 10;
    the unique linear detecting functional from the universal property. *)
Definition tensor_basis_coordinate b : {linear T -> K^o} :=
  abstract_tensor_family_lift hmu (tensor_basis_coefficient_multilinear b).

(** Source for [tensor_basis_coordinate_synthesis]: Federer 1.1.2,
    p. 10; coordinate detection on every finitely supported combination. *)
Lemma tensor_basis_coordinate_synthesis b (c : @free_vector K B) :
  tensor_basis_coordinate b (basis_synthesis tensor_family_basis c) = c b.
Proof.
apply: (free_linear_ext
  (linear_comp (tensor_basis_coordinate b) (basis_synthesis tensor_family_basis))
  (GRing.Linear.clone _ _ _ _ (@free_eval K B b) _)) c=> d /=.
rewrite basis_synthesisE /tensor_family_basis /tensor_basis_coordinate
  abstract_tensor_family_liftE tensor_basis_delta_product.
by rewrite /free_eval deltaE.
Qed.

(** Source for [tensor_family_basisP]: Federer 1.1.2, p. 10, final
    paragraph: products of basis vectors form a basis for any finite number
    of factors, also with infinite or empty individual basis index sets. *)
Theorem tensor_family_basisP : is_basis tensor_family_basis.
Proof.
apply/basisP; split.
- move=> c d h; apply/fsfunP=> b.
  by rewrite -!tensor_basis_coordinate_synthesis h.
- have hp : forall x, exists c, basis_synthesis tensor_family_basis c = mu x.
    apply: (@multilinear_basis_induction T mu (tensor_family_multilinear hmu)
      (fun t : T => exists c, basis_synthesis tensor_family_basis c = t)).
    * by exists 0; rewrite linear0.
    * move=> u v [c hc] [d hd]; exists (c+d); by rewrite linearD hc hd.
    * move=> a v [c hc]; exists (a *: c); by rewrite linearZ hc.
    * move=> b; exists (delta K b); exact: basis_synthesisE.
  apply: (tensor_family_induction hmu).
  * by exists 0; rewrite linear0.
  * move=> u v [c hc] [d hd]; exists (c+d); by rewrite linearD hc hd.
  * move=> a v [c hc]; exists (a *: c); by rewrite linearZ hc.
  * exact: hp.
Qed.
End Basis.
